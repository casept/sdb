/*
 * Host-side RSA authentication for sdb.
 *
 * A device running sdbd sends an AUTH token. The host signs it with a
 * private RSA key (~/.sdb/sdb_key). If the device does not know the key,
 * it asks the user to confirm it and stores it; the host then sends the
 * public key in the adb-compatible RSAPublicKey format.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <openssl/bn.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <openssl/rsa.h>

#include "fdevent.h"
#include "sysdeps.h"
#include "sdb.h"

#define SDB_AUTH_KEY_BITS 2048
#define SDB_AUTH_KEY_BYTES (SDB_AUTH_KEY_BITS / 8)
#define SDB_AUTH_KEY_NAME "sdb-host"

/* SHA-1 DigestInfo prefix, prepended to the 20-byte token before signing */
static const unsigned char sha1_digestinfo[] = {
    0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e, 0x03, 0x02, 0x1a,
    0x05, 0x00, 0x04, 0x14,
};

static char *sdb_auth_key_path(void)
{
    const char *home = getenv("HOME");
    char *path;

    if (!home) return NULL;
    path = malloc(strlen(home) + sizeof("/.sdb/sdb_key"));
    if (path) sprintf(path, "%s/.sdb/sdb_key", home);
    return path;
}

/* Loads the host key, generating and saving a new one on first use. */
static EVP_PKEY *sdb_auth_load_key(void)
{
    char *path = sdb_auth_key_path();
    EVP_PKEY *pkey = NULL;
    FILE *f;

    if (!path) return NULL;

    f = fopen(path, "r");
    if (f) {
        pkey = PEM_read_PrivateKey(f, NULL, NULL, NULL);
        fclose(f);
        free(path);
        return pkey;
    }

    /* First use: create ~/.sdb and a new key */
    {
        char dir[512];
        snprintf(dir, sizeof(dir), "%.*s", (int)(strrchr(path, '/') - path), path);
        sdb_mkdir(dir, 0700);
    }
    pkey = EVP_RSA_gen(SDB_AUTH_KEY_BITS);
    if (!pkey) {
        free(path);
        return NULL;
    }

    f = fopen(path, "w");
    if (f) {
        fchmod(fileno(f), 0600);
        PEM_write_PrivateKey(f, pkey, NULL, NULL, 0, NULL, NULL);
        fclose(f);
    }
    free(path);
    return pkey;
}

/* Writes the adb-style RSAPublicKey blob, base64 encoded, plus a name. */
int sdb_auth_public_key(char *out, size_t outlen)
{
    EVP_PKEY *pkey = sdb_auth_load_key();
    BIGNUM *n = NULL, *rr = NULL, *r2 = NULL, *exp = NULL;
    unsigned char blob[8 + 2 * SDB_AUTH_KEY_BYTES + 4];
    unsigned char n_bytes[SDB_AUTH_KEY_BYTES];
    unsigned char rr_bytes[SDB_AUTH_KEY_BYTES];
    uint32_t n0, inv, n0inv;
    unsigned int i;
    size_t b64len;
    int ok = 0;

    if (!pkey) return 0;
    if (!EVP_PKEY_get_bn_param(pkey, "n", &n)) goto out;
    if (!EVP_PKEY_get_bn_param(pkey, "e", &exp)) goto out;

    /* rr = 2^(2*KEYBITS) mod n */
    rr = BN_new();
    r2 = BN_new();
    if (!rr || !r2) goto out;
    BN_set_bit(r2, 2 * SDB_AUTH_KEY_BITS);
    BN_CTX *ctx = BN_CTX_new();
    if (!ctx || !BN_mod(rr, r2, n, ctx)) {
        BN_CTX_free(ctx);
        goto out;
    }
    BN_CTX_free(ctx);

    if (BN_bn2binpad(n, n_bytes, sizeof(n_bytes)) != sizeof(n_bytes)) goto out;
    if (BN_bn2binpad(rr, rr_bytes, sizeof(rr_bytes)) != sizeof(rr_bytes)) goto out;

    /* n0inv = -(n^-1) mod 2^32, via Newton iteration on the low word */
    n0 = (uint32_t)n_bytes[SDB_AUTH_KEY_BYTES - 4] |
         ((uint32_t)n_bytes[SDB_AUTH_KEY_BYTES - 3] << 8) |
         ((uint32_t)n_bytes[SDB_AUTH_KEY_BYTES - 2] << 16) |
         ((uint32_t)n_bytes[SDB_AUTH_KEY_BYTES - 1] << 24);
    inv = n0;
    for (i = 0; i < 5; i++) inv *= 2 - n0 * inv;
    n0inv = -inv;

    {
        unsigned char *p = blob;
        uint32_t words = SDB_AUTH_KEY_BITS / 32;
        uint32_t e = (uint32_t)BN_get_word(exp);
        /* little-endian words, modulus and rr stored little-endian */
        memcpy(p, &words, 4); p += 4;
        memcpy(p, &n0inv, 4); p += 4;
        for (i = 0; i < SDB_AUTH_KEY_BYTES; i++) *p++ = n_bytes[SDB_AUTH_KEY_BYTES - 1 - i];
        for (i = 0; i < SDB_AUTH_KEY_BYTES; i++) *p++ = rr_bytes[SDB_AUTH_KEY_BYTES - 1 - i];
        memcpy(p, &e, 4); p += 4;

        b64len = 4 * ((p - blob + 2) / 3) + 1;
        if (outlen < b64len + sizeof(" " SDB_AUTH_KEY_NAME)) goto out;
        EVP_EncodeBlock((unsigned char *)out, blob, (int)(p - blob));
        strcat(out, " " SDB_AUTH_KEY_NAME);
        ok = 1;
    }

out:
    BN_free(n);
    BN_free(rr);
    BN_free(r2);
    BN_free(exp);
    EVP_PKEY_free(pkey);
    return ok;
}

/* Signs the 20-byte token with PKCS#1 v1.5 over a SHA-1 DigestInfo. */
int sdb_auth_sign(const unsigned char *token, size_t tlen,
                  unsigned char *sig, size_t *siglen)
{
    EVP_PKEY *pkey = sdb_auth_load_key();
    EVP_PKEY_CTX *ctx = NULL;
    unsigned char digest_info[sizeof(sha1_digestinfo) + 20];
    int ok = 0;

    if (!pkey || tlen != 20) goto out;

    memcpy(digest_info, sha1_digestinfo, sizeof(sha1_digestinfo));
    memcpy(digest_info + sizeof(sha1_digestinfo), token, 20);

    ctx = EVP_PKEY_CTX_new(pkey, NULL);
    if (!ctx) goto out;
    if (EVP_PKEY_sign_init(ctx) <= 0) goto out;
    if (EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_PADDING) <= 0) goto out;
    if (EVP_PKEY_sign(ctx, sig, siglen, digest_info, sizeof(digest_info)) <= 0) goto out;
    ok = 1;

out:
    EVP_PKEY_CTX_free(ctx);
    EVP_PKEY_free(pkey);
    return ok;
}
