#include "int2048.h"

namespace sjtu {

static long long modPow(long long a, long long e, long long mod) {
  long long r = 1;
  while (e) {
    if (e & 1) r = (long long)((__int128)r * a % mod);
    a = (long long)((__int128)a * a % mod);
    e >>= 1;
  }
  return r;
}

static void ntt(std::vector<int> &a, bool invert, int mod, int primitiveRoot) {
  int n = (int)a.size();
  for (int i = 1, j = 0; i < n; ++i) {
    int bit = n >> 1;
    while (j & bit) {
      j ^= bit;
      bit >>= 1;
    }
    j ^= bit;
    if (i < j) {
      int t = a[i];
      a[i] = a[j];
      a[j] = t;
    }
  }

  for (int len = 2; len <= n; len <<= 1) {
    long long wlen = modPow(primitiveRoot, (mod - 1) / len, mod);
    if (invert) wlen = modPow(wlen, mod - 2, mod);
    for (int i = 0; i < n; i += len) {
      long long w = 1;
      int half = len >> 1;
      for (int j = 0; j < half; ++j) {
        int u = a[i + j];
        int v = (int)((__int128)a[i + j + half] * w % mod);
        int x = u + v;
        if (x >= mod) x -= mod;
        int y = u - v;
        if (y < 0) y += mod;
        a[i + j] = x;
        a[i + j + half] = y;
        w = (long long)((__int128)w * wlen % mod);
      }
    }
  }

  if (invert) {
    long long invN = modPow(n, mod - 2, mod);
    for (int i = 0; i < n; ++i) a[i] = (int)((__int128)a[i] * invN % mod);
  }
}

static std::vector<long long> convolution(const std::vector<int> &a, const std::vector<int> &b) {
  const int MOD1 = 998244353;
  const int ROOT1 = 3;
  const int MOD2 = 1004535809;
  const int ROOT2 = 3;

  int n = 1;
  while (n < (int)a.size() + (int)b.size()) n <<= 1;

  std::vector<int> x1(n, 0), y1(n, 0), x2(n, 0), y2(n, 0);
  for (int i = 0; i < (int)a.size(); ++i) {
    x1[i] = a[i] % MOD1;
    x2[i] = a[i] % MOD2;
  }
  for (int i = 0; i < (int)b.size(); ++i) {
    y1[i] = b[i] % MOD1;
    y2[i] = b[i] % MOD2;
  }

  ntt(x1, false, MOD1, ROOT1);
  ntt(y1, false, MOD1, ROOT1);
  ntt(x2, false, MOD2, ROOT2);
  ntt(y2, false, MOD2, ROOT2);

  for (int i = 0; i < n; ++i) {
    x1[i] = (int)((__int128)x1[i] * y1[i] % MOD1);
    x2[i] = (int)((__int128)x2[i] * y2[i] % MOD2);
  }

  ntt(x1, true, MOD1, ROOT1);
  ntt(x2, true, MOD2, ROOT2);

  long long invMOD1inMOD2 = modPow(MOD1, MOD2 - 2, MOD2);
  std::vector<long long> c(n);
  for (int i = 0; i < n; ++i) {
    long long a1 = x1[i];
    long long a2 = x2[i];
    long long t = (a2 - a1) % MOD2;
    if (t < 0) t += MOD2;
    t = (long long)((__int128)t * invMOD1inMOD2 % MOD2);
    c[i] = a1 + (long long)MOD1 * t;
  }
  return c;
}

void int2048::trim() {
  while (!d.empty() && d.back() == 0) d.pop_back();
  if (d.empty()) sign = false;
}

int int2048::absCmp(const int2048 &a, const int2048 &b) {
  if (a.d.size() != b.d.size()) return a.d.size() < b.d.size() ? -1 : 1;
  for (int i = (int)a.d.size() - 1; i >= 0; --i) {
    if (a.d[i] != b.d[i]) return a.d[i] < b.d[i] ? -1 : 1;
  }
  return 0;
}

int2048 int2048::absAdd(const int2048 &a, const int2048 &b) {
  int2048 c;
  c.sign = false;
  int n = (int)a.d.size();
  int m = (int)b.d.size();
  int sz = n > m ? n : m;
  c.d.resize(sz);
  int carry = 0;
  for (int i = 0; i < sz; ++i) {
    int x = i < n ? a.d[i] : 0;
    int y = i < m ? b.d[i] : 0;
    int cur = x + y + carry;
    if (cur >= BASE) {
      cur -= BASE;
      carry = 1;
    } else {
      carry = 0;
    }
    c.d[i] = cur;
  }
  if (carry) c.d.push_back(carry);
  c.trim();
  return c;
}

int2048 int2048::absSub(const int2048 &a, const int2048 &b) {
  int2048 c;
  c.sign = false;
  int n = (int)a.d.size();
  int m = (int)b.d.size();
  c.d.resize(n);
  int borrow = 0;
  for (int i = 0; i < n; ++i) {
    int x = a.d[i] - borrow;
    int y = i < m ? b.d[i] : 0;
    if (x < y) {
      x += BASE;
      borrow = 1;
    } else {
      borrow = 0;
    }
    c.d[i] = x - y;
  }
  c.trim();
  return c;
}

int2048 int2048::absMulInt(const int2048 &a, int m) {
  if (m == 0 || a.d.empty()) return int2048(0);
  int2048 c;
  c.sign = false;
  c.d.resize(a.d.size());
  long long carry = 0;
  for (int i = 0; i < (int)a.d.size(); ++i) {
    long long cur = 1LL * a.d[i] * m + carry;
    c.d[i] = (int)(cur % BASE);
    carry = cur / BASE;
  }
  while (carry) {
    c.d.push_back((int)(carry % BASE));
    carry /= BASE;
  }
  c.trim();
  return c;
}

void int2048::divModAbs(const int2048 &a, const int2048 &b, int2048 &q, int2048 &r) {
  q = int2048(0);
  r = int2048(0);
  if (b.d.empty()) return; // undefined by spec
  if (absCmp(a, b) < 0) {
    r = a;
    r.sign = false;
    return;
  }

  q.sign = false;
  q.d.assign(a.d.size(), 0);
  r.sign = false;
  r.d.clear();

  for (int i = (int)a.d.size() - 1; i >= 0; --i) {
    if (!r.d.empty()) {
      r.d.insert(r.d.begin(), a.d[i]);
    } else if (a.d[i] != 0) {
      r.d.push_back(a.d[i]);
    }
    r.trim();

    int ans = 0;
    if (absCmp(r, b) >= 0) {
      int m = (int)b.d.size();
      long long rHi = 0;
      if ((int)r.d.size() > m) {
        rHi = 1LL * r.d[m] * BASE + r.d[m - 1];
      } else {
        rHi = r.d[m - 1];
      }
      long long bHi = b.d[m - 1];
      ans = (int)(rHi / bHi);
      if (ans >= BASE) ans = BASE - 1;

      std::vector<int> prod(b.d.size() + 1, 0);
      auto buildProd = [&](int mul) {
        long long carry = 0;
        for (int j = 0; j < (int)b.d.size(); ++j) {
          long long cur = 1LL * b.d[j] * mul + carry;
          prod[j] = (int)(cur % BASE);
          carry = cur / BASE;
        }
        prod[b.d.size()] = (int)carry;
        while (!prod.empty() && prod.back() == 0) prod.pop_back();
      };
      auto cmpProdR = [&]() {
        if (prod.size() != r.d.size()) return prod.size() < r.d.size() ? -1 : 1;
        for (int k = (int)prod.size() - 1; k >= 0; --k) {
          if (prod[k] != r.d[k]) return prod[k] < r.d[k] ? -1 : 1;
        }
        return 0;
      };

      buildProd(ans);
      while (cmpProdR() > 0) {
        --ans;
        buildProd(ans);
      }
      q.d[i] = ans;
      if (ans) {
        int borrow = 0;
        for (int j = 0; j < (int)r.d.size(); ++j) {
          int y = j < (int)prod.size() ? prod[j] : 0;
          int x = r.d[j] - borrow;
          if (x < y) {
            x += BASE;
            borrow = 1;
          } else {
            borrow = 0;
          }
          r.d[j] = x - y;
        }
        r.trim();
      }
    }
  }

  q.trim();
  r.trim();
}

int2048::int2048() : sign(false) {}

int2048::int2048(long long x) : sign(false) {
  if (x == 0) return;
  unsigned long long t;
  if (x < 0) {
    sign = true;
    t = (unsigned long long)(-(x + 1)) + 1;
  } else {
    t = (unsigned long long)x;
  }
  while (t) {
    d.push_back((int)(t % BASE));
    t /= BASE;
  }
  trim();
}

int2048::int2048(const std::string &s) : sign(false) { read(s); }

int2048::int2048(const int2048 &o) : sign(o.sign), d(o.d) {}

void int2048::read(const std::string &s) {
  sign = false;
  d.clear();
  if (s.empty()) return;

  int pos = 0;
  if (s[0] == '-') {
    sign = true;
    pos = 1;
  } else if (s[0] == '+') {
    pos = 1;
  }

  while (pos < (int)s.size() && s[pos] == '0') ++pos;
  if (pos == (int)s.size()) {
    sign = false;
    return;
  }

  for (int i = (int)s.size(); i > pos; i -= WIDTH) {
    int l = i - WIDTH;
    if (l < pos) l = pos;
    int x = 0;
    for (int j = l; j < i; ++j) x = x * 10 + (s[j] - '0');
    d.push_back(x);
  }
  trim();
}

void int2048::print() { std::cout << *this; }

int2048 &int2048::add(const int2048 &o) { return (*this += o); }

int2048 add(int2048 a, const int2048 &b) { return a += b; }

int2048 &int2048::minus(const int2048 &o) { return (*this -= o); }

int2048 minus(int2048 a, const int2048 &b) { return a -= b; }

int2048 int2048::operator+() const { return *this; }

int2048 int2048::operator-() const {
  int2048 t(*this);
  if (!t.d.empty()) t.sign = !t.sign;
  return t;
}

int2048 &int2048::operator=(const int2048 &o) {
  if (this != &o) {
    sign = o.sign;
    d = o.d;
  }
  return *this;
}

int2048 &int2048::operator+=(const int2048 &o) {
  if (sign == o.sign) {
    int2048 t = absAdd(*this, o);
    t.sign = sign;
    *this = t;
  } else {
    int cmp = absCmp(*this, o);
    if (cmp == 0) {
      sign = false;
      d.clear();
    } else if (cmp > 0) {
      int2048 t = absSub(*this, o);
      t.sign = sign;
      *this = t;
    } else {
      int2048 t = absSub(o, *this);
      t.sign = o.sign;
      *this = t;
    }
  }
  trim();
  return *this;
}

int2048 operator+(int2048 a, const int2048 &b) { return a += b; }

int2048 &int2048::operator-=(const int2048 &o) {
  return (*this += (-o));
}

int2048 operator-(int2048 a, const int2048 &b) { return a -= b; }

int2048 &int2048::operator*=(const int2048 &o) {
  if (d.empty() || o.d.empty()) {
    sign = false;
    d.clear();
    return *this;
  }

  int n = (int)d.size();
  int m = (int)o.d.size();

  std::vector<int> res;

  if ((long long)n * m <= 120000) {
    res.assign(n + m, 0);
    for (int i = 0; i < n; ++i) {
      long long carry = 0;
      for (int j = 0; j < m || carry; ++j) {
        long long cur = res[i + j] + carry;
        if (j < m) cur += 1LL * d[i] * o.d[j];
        res[i + j] = (int)(cur % BASE);
        carry = cur / BASE;
      }
    }
  } else {
    std::vector<long long> conv = convolution(d, o.d);
    res.assign(conv.size() + 2, 0);
    long long carry = 0;
    for (int i = 0; i < (int)conv.size(); ++i) {
      long long cur = conv[i] + carry;
      res[i] = (int)(cur % BASE);
      carry = cur / BASE;
    }
    int idx = (int)conv.size();
    while (carry) {
      if (idx >= (int)res.size()) res.push_back(0);
      long long cur = res[idx] + carry;
      res[idx] = (int)(cur % BASE);
      carry = cur / BASE;
      ++idx;
    }
  }

  d = res;
  sign = (sign != o.sign);
  trim();
  return *this;
}

int2048 operator*(int2048 a, const int2048 &b) { return a *= b; }

int2048 &int2048::operator/=(const int2048 &o) {
  int2048 a(*this), b(o);
  a.sign = false;
  b.sign = false;

  int2048 q, r;
  divModAbs(a, b, q, r);

  bool neg = (sign != o.sign);
  bool hasRem = !r.d.empty();

  q.sign = false;
  if (neg) {
    if (hasRem) q += int2048(1);
    if (!q.d.empty()) q.sign = true;
  }
  q.trim();
  *this = q;
  return *this;
}

int2048 operator/(int2048 a, const int2048 &b) { return a /= b; }

int2048 &int2048::operator%=(const int2048 &o) {
  int2048 q = (*this) / o;
  *this -= q * o;
  trim();
  return *this;
}

int2048 operator%(int2048 a, const int2048 &b) { return a %= b; }

std::istream &operator>>(std::istream &is, int2048 &x) {
  std::string s;
  is >> s;
  x.read(s);
  return is;
}

std::ostream &operator<<(std::ostream &os, const int2048 &x) {
  if (x.d.empty()) {
    os << '0';
    return os;
  }
  if (x.sign) os << '-';
  os << x.d.back();
  char buf[16];
  for (int i = (int)x.d.size() - 2; i >= 0; --i) {
    std::snprintf(buf, sizeof(buf), "%06d", x.d[i]);
    os << buf;
  }
  return os;
}

bool operator==(const int2048 &a, const int2048 &b) {
  return a.sign == b.sign && a.d == b.d;
}

bool operator!=(const int2048 &a, const int2048 &b) { return !(a == b); }

bool operator<(const int2048 &a, const int2048 &b) {
  if (a.sign != b.sign) return a.sign;
  int cmp = int2048::absCmp(a, b);
  if (!a.sign) return cmp < 0;
  return cmp > 0;
}

bool operator>(const int2048 &a, const int2048 &b) { return b < a; }

bool operator<=(const int2048 &a, const int2048 &b) { return !(b < a); }

bool operator>=(const int2048 &a, const int2048 &b) { return !(a < b); }

} // namespace sjtu
