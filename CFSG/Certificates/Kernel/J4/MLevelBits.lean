module

public import CFSG.Certificates.Kernel.J4.DceS
public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KJ4.MLevel

open CFSG.KJ4 CFSG.KJ4.S

theorem land_pow (x k : ℕ) : Nat.land x (2 ^ k - 1) = x % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod x k

theorem land1 (x : ℕ) : Nat.land x 1 = x % 2 := land_pow x 1
theorem land255 (x : ℕ) : Nat.land x 255 = x % 256 := land_pow x 8
theorem land65535 (x : ℕ) : Nat.land x 65535 = x % 65536 := land_pow x 16
theorem landM32 (x : ℕ) : Nat.land x mask32 = x % 4294967296 := land_pow x 32
theorem landM144 (x : ℕ) : Nat.land x mask144 = x % 2 ^ 144 := land_pow x 144

theorem shr (x k : ℕ) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k
theorem shl (x k : ℕ) : Nat.shiftLeft x k = x * 2 ^ k := Nat.shiftLeft_eq x k

theorem lor_add {a b k : ℕ} (ha : a < 2 ^ k) (hb : b % 2 ^ k = 0) : Nat.lor a b = a + b := by
  have e : b = Nat.shiftLeft (b / 2 ^ k) k := by
    rw [shl]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb)).symm
  rw [e]
  change a ||| (b / 2 ^ k) <<< k = a + (b / 2 ^ k) <<< k
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.add_comm]

theorem or_add {a b k : ℕ} (ha : a < 2 ^ k) (hb : b % 2 ^ k = 0) : a ||| b = a + b := lor_add ha hb

theorem lor_comm' (a b : ℕ) : Nat.lor a b = Nat.lor b a := Nat.or_comm a b

theorem pow256 (i : ℕ) : 2 ^ (8 * i) = 256 ^ i := by
  rw [pow_mul]
  norm_num

theorem wLet_eq_div (X q : ℕ) : wLet X q = X / 256 ^ q % 256 := by
  change Nat.land (Nat.shiftRight X (8 * q)) 255 = _
  rw [land255, shr, pow256]

theorem mkC_eq {k : ℕ} (nd : ℕ) (hk : k < 4294967296) : mkC k nd = k + 4294967296 * nd := by
  change Nat.lor k (Nat.shiftLeft nd 32) = _
  rw [lor_add (k := 32) (by norm_num; omega) (by rw [shl]; simp), shl]
  ring

theorem cIdx_eq (x : ℕ) : cIdx x = x % 4294967296 := landM32 x

theorem cNd_eq (x : ℕ) : cNd x = x / 4294967296 % 4294967296 := by
  change Nat.land (Nat.shiftRight x 32) mask32 = _
  rw [landM32, shr]

theorem cIdx_mkC {k : ℕ} (nd : ℕ) (hk : k < 4294967296) : cIdx (mkC k nd) = k := by
  rw [cIdx_eq, mkC_eq nd hk]
  omega

theorem cNd_mkC {k nd : ℕ} (hk : k < 4294967296) (hn : nd < 4294967296) : cNd (mkC k nd) = nd := by
  rw [cNd_eq, mkC_eq nd hk]
  omega

theorem cIdx_lt (x : ℕ) : cIdx x < 4294967296 := by
  rw [cIdx_eq]
  omega

theorem cNd_lt (x : ℕ) : cNd x < 4294967296 := by
  rw [cNd_eq]
  omega

theorem cIdx_FAIL : cIdx FAIL = 2147483648 := by
  rw [cIdx_eq]
  rfl

theorem cIdx_mkC_succ {k nd : ℕ} (hk : k < 4294967296) :
    (k + 1 < 4294967296 ∧ cIdx (mkC (k + 1) nd) = k + 1) ∨ cIdx (mkC (k + 1) nd) = 0 := by
  rcases Nat.lt_or_ge (k + 1) 4294967296 with h | h
  · exact Or.inl ⟨h, cIdx_mkC nd h⟩
  · right
    have e : k + 1 = 4294967296 := by omega
    rw [cIdx_eq, e]
    change (Nat.lor 4294967296 (Nat.shiftLeft nd 32)) % 4294967296 = 0
    rw [shl]
    have : Nat.lor 4294967296 (nd * 2 ^ 32) = (1 ||| nd) * 2 ^ 32 := by
      change 4294967296 ||| nd * 2 ^ 32 = _
      rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_or_distrib, Nat.one_shiftLeft]
    rw [this]
    simp

theorem dD_eq {D : ℕ} (R : ℕ) (hD : D < 65536) : dD (D + 65536 * R) = D := by
  change Nat.land (D + 65536 * R) 65535 = D
  rw [land65535]
  omega

theorem shr16 {D : ℕ} (R : ℕ) (hD : D < 65536) : Nat.shiftRight (D + 65536 * R) 16 = R := by
  rw [shr]
  norm_num
  omega

theorem setD_eq {D D' : ℕ} (R : ℕ) (hD : D < 65536) (hD' : D' < 65536) :
    setD (D + 65536 * R) D' = D' + 65536 * R := by
  change Nat.lor (Nat.shiftLeft (Nat.shiftRight (D + 65536 * R) 16) 16) D' = _
  rw [shr16 R hD, lor_comm', lor_add (k := 16) (by norm_num; omega) (by rw [shl]; simp), shl]
  ring

theorem dD0_eq {D : ℕ} (R : ℕ) (hD : D < 65536) : dD0 (D + 65536 * R) = R % 65536 := by
  change Nat.land (Nat.shiftRight (D + 65536 * R) 16) 65535 = _
  rw [shr16 R hD, land65535]

theorem dK_eq {D : ℕ} (R : ℕ) (hD : D < 65536) :
    dK (D + 65536 * R) = R / 65536 % 4294967296 := by
  change Nat.land (Nat.shiftRight (D + 65536 * R) 32) mask32 = _
  rw [shr, landM32]
  norm_num
  omega

theorem dNd_eq {D : ℕ} (R : ℕ) (hD : D < 65536) :
    dNd (D + 65536 * R) = R / 281474976710656 % 4294967296 := by
  change Nat.land (Nat.shiftRight (D + 65536 * R) 64) mask32 = _
  rw [shr, landM32]
  norm_num
  omega

theorem dP0_eq {D : ℕ} (R : ℕ) (hD : D < 65536) :
    dP0 (D + 65536 * R) = R / 1208925819614629174706176 := by
  change Nat.shiftRight (D + 65536 * R) 96 = _
  rw [shr]
  norm_num
  omega

@[expose] def hdr (D0 K nd P0 : ℕ) : ℕ := D0 + 65536 * (K + 4294967296 * (nd + 4294967296 * P0))

theorem mkD_eq {D0 K nd P0 : ℕ} (hD : D0 < 65536) (hK : K < 4294967296) (hn : nd < 4294967296) :
    mkD D0 K nd P0 = D0 + 65536 * hdr D0 K nd P0 := by
  change Nat.lor D0 (Nat.lor (Nat.shiftLeft D0 16) (Nat.lor (Nat.shiftLeft K 32)
    (Nat.lor (Nat.shiftLeft nd 64) (Nat.shiftLeft P0 96)))) = _
  simp only [shl]
  norm_num
  rw [or_add (a := nd * 18446744073709551616) (k := 96) (by norm_num; omega) (by norm_num),
    or_add (a := K * 4294967296) (k := 64) (by norm_num; omega) (by norm_num; omega),
    or_add (a := D0 * 65536) (k := 32) (by norm_num; omega) (by norm_num; omega),
    or_add (a := D0) (k := 16) (by norm_num; omega) (by norm_num; omega)]
  unfold hdr
  ring

theorem hdr_D0 {D0 K nd P0 : ℕ} (hD : D0 < 65536) : hdr D0 K nd P0 % 65536 = D0 := by
  unfold hdr
  omega

theorem hdr_K {D0 K nd P0 : ℕ} (hD : D0 < 65536) (hK : K < 4294967296) :
    hdr D0 K nd P0 / 65536 % 4294967296 = K := by
  unfold hdr
  omega

theorem hdr_nd {D0 K nd P0 : ℕ} (hD : D0 < 65536) (hK : K < 4294967296) (hn : nd < 4294967296) :
    hdr D0 K nd P0 / 281474976710656 % 4294967296 = nd := by
  unfold hdr
  omega

theorem hdr_P0 {D0 K nd P0 : ℕ} (hD : D0 < 65536) (hK : K < 4294967296) (hn : nd < 4294967296) :
    hdr D0 K nd P0 / 1208925819614629174706176 = P0 := by
  unfold hdr
  omega

@[expose] def rem (W n i : ℕ) : ℕ := W / 256 ^ i + 254 * 256 ^ (n - i)

@[expose] def cur (W n i f : ℕ) : ℕ := f + 2 * rem W n i

theorem rem_div {W n i q : ℕ} (h : i + q ≤ n) : rem W n i / 256 ^ q = rem W n (i + q) := by
  unfold rem
  have e : 256 ^ (n - i) = 256 ^ (n - (i + q)) * 256 ^ q := by
    rw [← pow_add]
    congr 1
    omega
  rw [e, ← mul_assoc, Nat.add_mul_div_right _ _ (pow_pos (by norm_num) q), Nat.div_div_eq_div_mul,
    ← pow_add]

theorem rem_mod {W n i : ℕ} (hW : W < 256 ^ n) (hi : i ≤ n) :
    rem W n i % 256 = if i < n then wLet W i else 254 := by
  unfold rem
  split_ifs with h
  · rw [wLet_eq_div]
    have e : 256 ^ (n - i) = 256 * 256 ^ (n - i - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have e2 : 254 * (256 * 256 ^ (n - i - 1)) = 256 * (254 * 256 ^ (n - i - 1)) := by ring
    rw [e, e2, Nat.add_mul_mod_self_left]
  · have e : i = n := by omega
    subst e
    rw [Nat.div_eq_of_lt hW]
    simp

theorem shr1_cur {W n i f : ℕ} (hf : f ≤ 1) : Nat.shiftRight (cur W n i f) 1 = rem W n i := by
  rw [shr]
  unfold cur
  omega

theorem cur_bit {W n i f : ℕ} (hf : f ≤ 1) : Nat.land (cur W n i f) 1 = f := by
  rw [land1]
  unfold cur
  omega

theorem letAt_cur {W n i f : ℕ} (hW : W < 256 ^ n) (hf : f ≤ 1) (hi : i ≤ n) :
    letAt (cur W n i f) = if i < n then wLet W i else 254 := by
  change Nat.land (Nat.shiftRight (cur W n i f) 1) 255 = _
  rw [shr1_cur hf, land255, rem_mod hW hi]

theorem letAt_lt {W n i f c : ℕ} (hW : W < 256 ^ n) (hf : f ≤ 1) (hi : i ≤ n)
    (h : letAt (cur W n i f) = c) (hc : c ≠ 254) : i < n ∧ wLet W i = c := by
  rw [letAt_cur hW hf hi] at h
  split_ifs at h with h'
  · exact ⟨h', h⟩
  · exact absurd h.symm hc

theorem adv_cur {W n i f m S : ℕ} (hf : f ≤ 1) (hS : S ≤ 1) (h : i + m ≤ n) :
    adv (cur W n i f) m S = cur W n (i + m) (Nat.lor f S) := by
  have hfS : Nat.lor f S ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hf with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with rfl | rfl <;> decide
  change Nat.lor (Nat.lor (Nat.land (cur W n i f) 1) S)
    (Nat.shiftLeft (Nat.shiftRight (cur W n i f) (1 + 8 * m)) 1) = _
  have e0 : cur W n i f / 2 = rem W n i := by
    unfold cur
    omega
  have e1 : cur W n i f / 2 ^ (1 + 8 * m) = rem W n (i + m) := by
    rw [pow_add, pow_one, ← Nat.div_div_eq_div_mul, e0, pow256, rem_div h]
  rw [cur_bit hf, shr, e1, shl, lor_add (k := 1) (by omega) (by simp)]
  unfold cur
  ring

theorem letsAt_cur {W n i f m : ℕ} (hf : f ≤ 1) : letsAt (cur W n i f) m = rem W n i % 256 ^ m := by
  change Nat.land (Nat.shiftRight (cur W n i f) 1) (Nat.shiftLeft 1 (8 * m) - 1) = _
  rw [shr1_cur hf, shl, one_mul, land_pow, pow256]

theorem wLet_mod {X m q : ℕ} (hq : q < m) : wLet (X % 256 ^ m) q = wLet X q := by
  rw [wLet_eq_div, wLet_eq_div]
  have e : 256 ^ m = 256 ^ q * 256 ^ (m - q) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self 256 (by omega)

theorem wLet_rem {W n i q : ℕ} (hW : W < 256 ^ n) (h : i + q ≤ n) :
    wLet (rem W n i) q = if i + q < n then wLet W (i + q) else 254 := by
  rw [wLet_eq_div, rem_div h, rem_mod hW h]

theorem seg_match {W n i f m u : ℕ} (hW : W < 256 ^ n) (hf : f ≤ 1) (hi : i ≤ n)
    (hu : ∀ q < m, wLet u q < 4) (h : letsAt (cur W n i f) m = u) :
    i + m ≤ n ∧ ∀ q < m, wLet W (i + q) = wLet u q := by
  rw [letsAt_cur hf] at h
  have key : ∀ q < m, i + q ≤ n → wLet u q = if i + q < n then wLet W (i + q) else 254 := by
    intro q hq hiq
    rw [← h, wLet_mod hq, wLet_rem hW hiq]
  have him : i + m ≤ n := by
    by_contra hc
    have h1 := key (n - i) (by omega) (by omega)
    have hn : ¬ (i + (n - i) < n) := by omega
    rw [ite_eq_right hn] at h1
    have := hu (n - i) (by omega)
    omega
  refine ⟨him, fun q hq => ?_⟩
  have hl : i + q < n := by omega
  rw [key q hq (by omega), ite_eq_left hl]

theorem cur_end {W n i f : ℕ} (hf : f ≤ 1) (hi : i ≤ n) (h : cur W n i f = 509) : i = n ∧ f = 1 := by
  unfold cur rem at h
  generalize W / 256 ^ i = a at h
  have h1 : 256 ≤ 256 ^ (n - i) ∨ n - i = 0 := by
    rcases Nat.eq_zero_or_pos (n - i) with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (le_self_pow₀ (by norm_num) (by omega))
  rcases h1 with h1 | h1
  · omega
  · rw [h1, pow_zero] at h
    omega

theorem wInit_cur {W n : ℕ} (hW : W < 256 ^ n) : wInit W n = cur W n 0 0 := by
  change Nat.shiftLeft (Nat.lor W (Nat.shiftLeft 254 (8 * n))) 1 = _
  rw [shl 254, pow256, lor_add (k := 8 * n) (by rw [pow256]; exact hW) (by rw [pow256]; simp), shl]
  unfold cur rem
  simp
  ring

theorem wInit_or1 {W n : ℕ} (hW : W < 256 ^ n) : Nat.lor (wInit W n) 1 = cur W n 0 1 := by
  rw [wInit_cur hW, lor_comm']
  unfold cur
  rw [lor_add (k := 1) (by norm_num) (by omega)]
  omega

end CFSG.KJ4.MLevel

end
