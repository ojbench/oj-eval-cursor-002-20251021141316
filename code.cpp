#include <bits/stdc++.h>
// Merged implementation for OJ: int2048 class
namespace sjtu {
class int2048 {
private:
  static const uint32_t BASE = 1000000000u;
  static const int BASE_DIGS = 9;
  std::vector<uint32_t> digits;
  bool negative = false;

  void trim() {
    while (!digits.empty() && digits.back() == 0) digits.pop_back();
    if (digits.empty()) negative = false;
  }
  bool isZero() const { return digits.empty(); }
  int absCompare(const int2048 &other) const {
    if (digits.size() != other.digits.size())
      return digits.size() < other.digits.size() ? -1 : 1;
    for (size_t i = digits.size(); i-- > 0;) {
      if (digits[i] != other.digits[i]) return digits[i] < other.digits[i] ? -1 : 1;
    }
    return 0;
  }
  void absAdd(const int2048 &other) {
    uint64_t carry = 0;
    const size_t n = std::max(digits.size(), other.digits.size());
    if (digits.size() < n) digits.resize(n, 0);
    for (size_t i = 0; i < n; ++i) {
      uint64_t a = digits[i];
      uint64_t b = (i < other.digits.size() ? other.digits[i] : 0);
      uint64_t sum = a + b + carry;
      digits[i] = static_cast<uint32_t>(sum % BASE);
      carry = sum / BASE;
    }
    if (carry) digits.push_back(static_cast<uint32_t>(carry));
  }
  void absSub(const int2048 &other) {
    int64_t carry = 0;
    for (size_t i = 0; i < digits.size(); ++i) {
      int64_t a = digits[i];
      int64_t b = (i < other.digits.size() ? other.digits[i] : 0);
      int64_t cur = a - b + carry;
      if (cur < 0) { cur += BASE; carry = -1; } else { carry = 0; }
      digits[i] = static_cast<uint32_t>(cur);
    }
    trim();
  }
  static void mulSchoolbook(const std::vector<uint32_t> &a,
                            const std::vector<uint32_t> &b,
                            std::vector<uint32_t> &out) {
    out.assign(a.size() + b.size(), 0);
    for (size_t i = 0; i < a.size(); ++i) {
      uint64_t carry = 0, ai = a[i];
      for (size_t j = 0; j < b.size(); ++j) {
        uint64_t cur = out[i + j] + ai * (uint64_t)b[j] + carry;
        out[i + j] = (uint32_t)(cur % BASE);
        carry = cur / BASE;
      }
      size_t pos = i + b.size();
      while (carry) {
        if (pos >= out.size()) out.push_back(0);
        uint64_t cur = out[pos] + carry;
        out[pos] = (uint32_t)(cur % BASE);
        carry = cur / BASE;
        ++pos;
      }
    }
    while (!out.empty() && out.back() == 0) out.pop_back();
  }
  static void divmodTrunc(const int2048 &A, const int2048 &B, int2048 &Q, int2048 &R) {
    int2048 a = A; a.negative = false; a.trim();
    int2048 b = B; b.negative = false; b.trim();
    Q.digits.clear(); Q.negative = false;
    R = a;
    if (b.isZero()) return;
    if (R.absCompare(b) < 0) { Q.digits.clear(); Q.negative = false; return; }
    if (b.digits.size() == 1) {
      uint64_t divv = b.digits[0];
      Q.digits.assign(R.digits.size(), 0);
      uint64_t rem = 0;
      for (size_t i = R.digits.size(); i-- > 0;) {
        uint64_t cur = R.digits[i] + rem * BASE;
        uint64_t qd = cur / divv;
        rem = cur % divv;
        Q.digits[i] = (uint32_t)qd;
      }
      R.digits.clear();
      if (rem) R.digits.push_back((uint32_t)rem);
      Q.trim(); R.trim();
    } else {
      size_t n = R.digits.size();
      size_t m = b.digits.size();
      Q.digits.assign(n - m + 1, 0);
      R.digits.push_back(0);
      for (size_t pos = n - m + 1; pos-- > 0;) {
        uint64_t r_hi = (pos + m < R.digits.size() ? R.digits[pos + m] : 0);
        uint64_t r2 = R.digits[pos + m - 1];
        uint64_t v1 = b.digits[m - 1];
        __int128 numerator = (__int128)r_hi * BASE + r2;
        uint64_t qhat = (uint64_t)(numerator / v1);
        if (qhat >= BASE) qhat = BASE - 1;
        while (true) {
          std::vector<uint32_t> Rc = R.digits;
          uint64_t carry = 0; bool ok = true;
          for (size_t i = 0; i < m; ++i) {
            __int128 prod = (__int128)b.digits[i] * (__int128)qhat + (__int128)carry;
            uint64_t p_lo = (uint64_t)(prod % BASE);
            carry = (uint64_t)(prod / BASE);
            size_t idx = pos + i;
            if (Rc[idx] < p_lo) {
              uint64_t need = (uint64_t)BASE + Rc[idx];
              Rc[idx] = (uint32_t)(need - p_lo);
              size_t k = idx + 1;
              while (true) {
                if (k >= Rc.size()) { ok = false; break; }
                if (Rc[k] == 0) { Rc[k] = BASE - 1; ++k; }
                else { --Rc[k]; break; }
              }
              if (!ok) break;
            } else {
              Rc[idx] = (uint32_t)(Rc[idx] - p_lo);
            }
          }
          if (ok) {
            size_t idx = pos + m;
            while (carry) {
              if (idx >= Rc.size()) { ok = false; break; }
              if (Rc[idx] < carry) {
                uint64_t need = (uint64_t)BASE + Rc[idx];
                Rc[idx] = (uint32_t)(need - carry);
                carry = 1; ++idx;
              } else {
                Rc[idx] = (uint32_t)(Rc[idx] - carry);
                carry = 0; break;
              }
            }
          }
          if (ok) { R.digits.swap(Rc); Q.digits[pos] = (uint32_t)qhat; break; }
          if (qhat == 0) { Q.digits[pos] = 0; break; }
          --qhat;
        }
      }
      R.trim(); Q.trim();
    }
    if (!Q.isZero()) Q.negative = (A.negative != B.negative); else Q.negative = false;
    if (!R.isZero()) R.negative = A.negative; else R.negative = false;
  }
public:
  int2048() {}
  int2048(long long v) {
    if (v == 0) { negative = false; return; }
    if (v < 0) { negative = true; unsigned long long u = (unsigned long long)(-(v + 1)); u += 1ull; while (u) { digits.push_back((uint32_t)(u % BASE)); u /= BASE; } }
    else { unsigned long long u = (unsigned long long)v; while (u) { digits.push_back((uint32_t)(u % BASE)); u /= BASE; } }
  }
  int2048(const std::string &s) { read(s); }
  int2048(const int2048 &o) = default;

  void read(const std::string &s) {
    digits.clear(); negative = false; size_t i = 0;
    while (i < s.size() && (s[i] == ' ' || s[i] == '\n' || s[i] == '\t' || s[i] == '\r')) ++i;
    bool neg = false; if (i < s.size() && (s[i] == '+' || s[i] == '-')) { neg = (s[i] == '-'); ++i; }
    while (i < s.size() && s[i] == '0') ++i;
    std::vector<uint32_t> parts;
    for (size_t j = s.size(); j > i;) {
      size_t start = (j >= (size_t)BASE_DIGS ? j - BASE_DIGS : 0); if (start < i) start = i;
      uint32_t x = 0; for (size_t k = start; k < j; ++k) { char c = s[k]; if (c < '0' || c > '9') { x = 0; break; } x = x * 10u + (uint32_t)(c - '0'); }
      parts.push_back(x); j = start; if (j == i) break;
    }
    for (size_t idx = 0; idx < parts.size(); ++idx) digits.push_back(parts[idx]);
    trim(); if (!digits.empty()) negative = neg;
  }
  void print() {
    if (digits.empty()) { std::cout << 0; return; }
    if (negative) std::cout << '-';
    size_t i = digits.size() - 1; std::cout << digits[i];
    while (i-- > 0) { uint32_t x = digits[i]; char buf[32]; std::snprintf(buf, sizeof(buf), "%0*u", BASE_DIGS, x); std::cout << buf; }
  }

  int2048 &add(const int2048 &o) {
    if (o.isZero()) return *this; if (isZero()) { *this = o; return *this; }
    if (negative == o.negative) { absAdd(o); }
    else { int cmp = absCompare(o); if (cmp == 0) { digits.clear(); negative = false; return *this; } if (cmp > 0) { absSub(o); } else { int2048 tmp = o; tmp.absSub(*this); *this = tmp; } }
    return *this;
  }
  friend int2048 add(int2048 a, const int2048 &b) { return a.add(b); }

  int2048 &minus(const int2048 &o) { if (o.isZero()) return *this; int2048 t = o; if (!t.isZero()) t.negative = !t.negative; return this->add(t); }
  friend int2048 minus(int2048 a, const int2048 &b) { return a.minus(b); }

  int2048 operator+() const { return *this; }
  int2048 operator-() const { int2048 r = *this; if (!r.isZero()) r.negative = !r.negative; return r; }
  int2048 &operator=(const int2048 &o) = default;
  int2048 &operator+=(const int2048 &rhs) { return this->add(rhs); }
  friend int2048 operator+(int2048 a, const int2048 &b) { return a += b; }
  int2048 &operator-=(const int2048 &rhs) { return this->minus(rhs); }
  friend int2048 operator-(int2048 a, const int2048 &b) { return a -= b; }
  int2048 &operator*=(const int2048 &rhs) { if (this->isZero() || rhs.isZero()) { digits.clear(); negative = false; return *this; } std::vector<uint32_t> prod; mulSchoolbook(this->digits, rhs.digits, prod); digits.swap(prod); negative = (negative != rhs.negative); trim(); return *this; }
  friend int2048 operator*(int2048 a, const int2048 &b) { return a *= b; }
  int2048 &operator/=(const int2048 &rhs) { if (rhs.isZero()) return *this; if (this->isZero()) { digits.clear(); negative = false; return *this; } int2048 q, r; divmodTrunc(*this, rhs, q, r); bool signsDifferent = (this->negative != rhs.negative); if (signsDifferent && !r.isZero()) { q = q.minus(int2048(1)); } *this = q; return *this; }
  friend int2048 operator/(int2048 a, const int2048 &b) { return a /= b; }
  int2048 &operator%=(const int2048 &rhs) { if (rhs.isZero()) return *this; if (this->isZero()) { digits.clear(); negative = false; return *this; } int2048 q, r; divmodTrunc(*this, rhs, q, r); bool signsDifferent = (this->negative != rhs.negative); if (signsDifferent && !r.isZero()) { r.add(rhs); } *this = r; return *this; }
  friend int2048 operator%(int2048 a, const int2048 &b) { return a %= b; }
  friend std::istream &operator>>(std::istream &in, int2048 &x) { std::string s; in >> s; x.read(s); return in; }
  friend std::ostream &operator<<(std::ostream &out, const int2048 &x) { if (x.digits.empty()) { out << 0; return out; } if (x.negative) out << '-'; size_t i = x.digits.size() - 1; out << x.digits[i]; while (i-- > 0) { uint32_t val = x.digits[i]; char buf[32]; std::snprintf(buf, sizeof(buf), "%0*u", BASE_DIGS, val); out << buf; } return out; }
  friend bool operator==(const int2048 &a, const int2048 &b) { return a.negative == b.negative && a.digits == b.digits; }
  friend bool operator!=(const int2048 &a, const int2048 &b) { return !(a == b); }
  friend bool operator<(const int2048 &a, const int2048 &b) { if (a.negative != b.negative) return a.negative; int cmp = a.absCompare(b); if (a.negative) return cmp > 0; return cmp < 0; }
  friend bool operator>(const int2048 &a, const int2048 &b) { return b < a; }
  friend bool operator<=(const int2048 &a, const int2048 &b) { return !(b < a); }
  friend bool operator>=(const int2048 &a, const int2048 &b) { return !(a < b); }
};
} // namespace sjtu

// Simple main for OJ compatibility if needed (may be ignored by OJ)
int main() { return 0; }
