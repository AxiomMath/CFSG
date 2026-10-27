module

public import Certificates.Data.Kernel.S1277KML
public import CFSG.Certificates.Kernel.S1277KGmSound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

namespace CFSG.KS.S1277ML

open CFSG.KC.S1277ML

def bsum (W : ℕ) (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bsum W c n + c n * 2 ^ (W * n)

theorem bsum_lt {W : ℕ} {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) : ∀ n,
    bsum W c n < 2 ^ (W * n)
  | 0 => by simp [bsum]
  | n + 1 => by
    have h1 := bsum_lt hc n
    have h2 : c n * 2 ^ (W * n) ≤ (2 ^ W - 1) * 2 ^ (W * n) :=
      Nat.mul_le_mul_right _ (by have := hc n; omega)
    have hW : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have e : 2 ^ (W * (n + 1)) = (2 ^ W - 1) * 2 ^ (W * n) + 2 ^ (W * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (2 ^ (W * n))]
      have : 2 ^ (W * n) ≤ 2 ^ W * 2 ^ (W * n) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [bsum, e]
    omega

theorem testBit_bsum {W : ℕ} (hW : 0 < W) {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) (p : ℕ) :
    ∀ n, (bsum W c n).testBit p = (decide (p < W * n) && (c (p / W)).testBit (p % W))
  | 0 => by simp [bsum]
  | n + 1 => by
    rw [bsum, Nat.add_comm, Nat.mul_comm (c n),
      Nat.testBit_two_pow_mul_add _ (bsum_lt hc n)]
    by_cases h : p < W * n
    · simp only [h, ↓reduceIte]
      rw [testBit_bsum hW hc p n]
      have h' : p < W * (n + 1) := by rw [Nat.mul_succ]; omega
      simp [h, h']
    · simp only [h, ↓reduceIte]
      by_cases h2 : p < W * (n + 1)
      · have e1 : p / W = n := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega)
          (by rw [Nat.succ_mul, Nat.mul_comm]; rw [Nat.mul_succ] at h2; omega)
        have e2 : p % W = p - W * n := by
          have := Nat.div_add_mod p W
          rw [e1] at this
          omega
        simp [h2, e1, e2]
      · have h3 : (c n).testBit (p - W * n) = false := by
          refine Nat.testBit_lt_two_pow (lt_of_lt_of_le (hc n) ?_)
          exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ] at h2; omega)
        simp [h2, h3]

theorem bsum_add (W : ℕ) (a b : ℕ → ℕ) : ∀ n,
    bsum W a n + bsum W b n = bsum W (fun i => a i + b i) n
  | 0 => rfl
  | n + 1 => by
    rw [bsum, bsum, bsum, ← bsum_add W a b n]
    ring

theorem bsum_lin (W k : ℕ) (a b : ℕ → ℕ) : ∀ n,
    bsum W (fun i => a i + k * b i) n = bsum W a n + k * bsum W b n
  | 0 => rfl
  | n + 1 => by
    rw [bsum, bsum, bsum, bsum_lin W k a b n]
    ring

theorem bsum_pair (W : ℕ) (c : ℕ → ℕ) : ∀ n,
    bsum W c (2 * n) = bsum (2 * W) (fun B => c (2 * B) + 2 ^ W * c (2 * B + 1)) n
  | 0 => rfl
  | n + 1 => by
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, bsum, bsum, bsum, bsum_pair W c n]
    ring

theorem bsum_and {W n : ℕ} (hW : 0 < W) {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) {M : ℕ}
    (hM : ∀ p, M.testBit p = (decide (p < 2 * W * n) && decide (p % (2 * W) < W))) :
    bsum W c (2 * n) &&& M = bsum (2 * W) (fun B => c (2 * B)) n := by
  have hc2 : ∀ B, c (2 * B) < 2 ^ (2 * W) :=
    fun B => lt_of_lt_of_le (hc _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, testBit_bsum hW hc, hM, testBit_bsum (by omega) hc2]
  have e : W * (2 * n) = 2 * W * n := by ring
  rw [e]
  have hp : p = p % (2 * W) + W * (2 * (p / (2 * W))) := by
    have := Nat.div_add_mod p (2 * W)
    calc p = 2 * W * (p / (2 * W)) + p % (2 * W) := this.symm
      _ = p % (2 * W) + W * (2 * (p / (2 * W))) := by ring
  have hr2 : p % (2 * W) < 2 * W := Nat.mod_lt _ (by omega)
  by_cases hr : p % (2 * W) < W
  · have e1 : p / W = 2 * (p / (2 * W)) := by
      conv_lhs => rw [hp]
      rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
    have e2 : p % W = p % (2 * W) := by
      conv_lhs => rw [hp]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    rw [e1, e2]
    by_cases hpn : p < 2 * W * n <;> simp [hr, hpn]
  · have h3 : (c (2 * (p / (2 * W)))).testBit (p % (2 * W)) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hc _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hr, h3]

theorem bsum_shr_and {W n : ℕ} (hW : 0 < W) {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) {M : ℕ}
    (hM : ∀ p, M.testBit p = (decide (p < 2 * W * n) && decide (p % (2 * W) < W))) :
    (bsum W c (2 * n) >>> W) &&& M = bsum (2 * W) (fun B => c (2 * B + 1)) n := by
  have hc2 : ∀ B, c (2 * B + 1) < 2 ^ (2 * W) :=
    fun B => lt_of_lt_of_le (hc _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_bsum hW hc, hM, testBit_bsum (by omega) hc2]
  have e : W * (2 * n) = 2 * W * n := by ring
  rw [e]
  have hp : p = p % (2 * W) + W * (2 * (p / (2 * W))) := by
    have := Nat.div_add_mod p (2 * W)
    calc p = 2 * W * (p / (2 * W)) + p % (2 * W) := this.symm
      _ = p % (2 * W) + W * (2 * (p / (2 * W))) := by ring
  have hr2 : p % (2 * W) < 2 * W := Nat.mod_lt _ (by omega)
  by_cases hr : p % (2 * W) < W
  · have hp' : W + p = p % (2 * W) + W * (2 * (p / (2 * W)) + 1) := by
      conv_lhs => rw [hp]
      ring
    have e1 : (W + p) / W = 2 * (p / (2 * W)) + 1 := by
      rw [hp', Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
    have e2 : (W + p) % W = p % (2 * W) := by
      rw [hp', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    rw [e1, e2]
    by_cases hpn : p < 2 * W * n
    · have hq : p / (2 * W) < n := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc p < 2 * W * n := hpn
          _ = n * (2 * W) := by ring
      have hlt : W + p < 2 * W * n := by
        have h4 : W * (2 * (p / (2 * W)) + 1) + W ≤ 2 * W * n := by
          have : p / (2 * W) + 1 ≤ n := hq
          calc W * (2 * (p / (2 * W)) + 1) + W = 2 * W * (p / (2 * W) + 1) := by ring
            _ ≤ 2 * W * n := Nat.mul_le_mul_left _ this
        omega
      simp [hr, hpn, hlt]
    · simp [hpn]
  · have h3 : (c (2 * (p / (2 * W)) + 1)).testBit (p % (2 * W)) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hc _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hr, h3]

theorem bsum_shr {W : ℕ} (hW : 0 < W) {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) (n : ℕ) :
    bsum W c (n + 1) >>> W = bsum W (fun i => c (i + 1)) n := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_shiftRight, testBit_bsum hW hc, testBit_bsum hW (fun b => hc (b + 1))]
  have e1 : (W + p) / W = p / W + 1 := by rw [Nat.add_comm W p, Nat.add_div_right _ hW]
  have e2 : (W + p) % W = p % W := by rw [Nat.add_comm W p, Nat.add_mod_right]
  have e3 : decide (W + p < W * (n + 1)) = decide (p < W * n) :=
    decide_eq_decide.2 (by rw [Nat.mul_succ]; omega)
  rw [e1, e2, e3]

def cnt (x : ℕ) : ℕ → ℕ → ℕ
  | 0, b => (x.testBit b).toNat
  | k + 1, b => cnt x k (2 * b) + cnt x k (2 * b + 1)

theorem cnt_eq (x : ℕ) : ∀ k b,
    cnt x k b = ((List.range (2 ^ k)).filter fun j => x.testBit (b * 2 ^ k + j)).length
  | 0, b => by
    simp only [cnt, Nat.pow_zero, Nat.mul_one, List.range_one, List.filter_cons, List.filter_nil,
      Nat.add_zero]
    cases x.testBit b <;> rfl
  | k + 1, b => by
    rw [cnt, cnt_eq x k, cnt_eq x k, Nat.pow_succ, Nat.mul_two, List.range_add, List.filter_append,
      List.length_append, List.filter_map, List.length_map]
    congr 2
    · apply List.filter_congr
      intro j _
      congr 1
      ring
    · apply List.filter_congr
      intro j _
      simp only [Function.comp]
      congr 1
      ring

theorem cnt_le (x k b : ℕ) : cnt x k b ≤ 2 ^ k := by
  rw [cnt_eq]
  exact (List.length_filter_le _ _).trans (by simp)

theorem cnt_lt (x k b : ℕ) : cnt x k b < 2 ^ 2 ^ k :=
  lt_of_le_of_lt (cnt_le x k b) (Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self)

theorem mask_spec {M n : ℕ} (f : ℕ → Bool) (hM : M < 2 ^ n) (hf : ∀ p, n ≤ p → f p = false)
    (h : ∀ p < n, M.testBit p = f p) : ∀ p, M.testBit p = f p := by
  intro p
  by_cases hp : p < n
  · exact h p hp
  · rw [hf p (by omega), Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) (by omega)))]

def pc1 (m : ℕ) : ℕ := m - ((m >>> 1) &&& 6148914691236517205)

def pc2 (x : ℕ) : ℕ := (x &&& 3689348814741910323) + ((x >>> 2) &&& 3689348814741910323)

def pc3 (x : ℕ) : ℕ := (x + (x >>> 4)) &&& 1085102592571150095

def pc4 (x : ℕ) : ℕ := ((x * 72340172838076673) &&& 18446744073709551615) >>> 56

theorem pcN_def (m : ℕ) : pcN m = pc4 (pc3 (pc2 (pc1 m))) := rfl

theorem hM1 : ∀ p, (6148914691236517205 : ℕ).testBit p =
    (decide (p < 2 * 1 * 32) && decide (p % (2 * 1) < 1)) :=
  mask_spec (n := 64) _ (by norm_num)
    (fun p hp => by have : ¬ p < 2 * 1 * 32 := by omega
                    simp [this]) (by decide)

theorem hM2 : ∀ p, (3689348814741910323 : ℕ).testBit p =
    (decide (p < 2 * 2 * 16) && decide (p % (2 * 2) < 2)) :=
  mask_spec (n := 64) _ (by norm_num)
    (fun p hp => by have : ¬ p < 2 * 2 * 16 := by omega
                    simp [this]) (by decide)

theorem hM4 : ∀ p, (1085102592571150095 : ℕ).testBit p =
    (decide (p < 2 * 4 * 8) && decide (p % (2 * 4) < 4)) :=
  mask_spec (n := 64) _ (by norm_num)
    (fun p hp => by have : ¬ p < 2 * 4 * 8 := by omega
                    simp [this]) (by decide)

theorem pc1_bsum {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ 1) :
    pc1 (bsum 1 c (2 * 32)) = bsum 2 (fun B => c (2 * B) + c (2 * B + 1)) 32 := by
  have hY : (bsum 1 c (2 * 32) >>> 1) &&& 6148914691236517205 =
      bsum 2 (fun B => c (2 * B + 1)) 32 :=
    bsum_shr_and (W := 1) (n := 32) Nat.one_pos hc hM1
  have hx : bsum 1 c (2 * 32) =
      bsum 2 (fun B => c (2 * B)) 32 + 2 * bsum 2 (fun B => c (2 * B + 1)) 32 := by
    rw [bsum_pair 1 c 32]
    exact bsum_lin 2 2 (fun B => c (2 * B)) (fun B => c (2 * B + 1)) 32
  have h2 : bsum 2 (fun B => c (2 * B) + c (2 * B + 1)) 32 =
      bsum 2 (fun B => c (2 * B)) 32 + bsum 2 (fun B => c (2 * B + 1)) 32 :=
    (bsum_add _ _ _ _).symm
  rw [pc1, hY, h2]
  omega

theorem pc2_bsum {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ 2) :
    pc2 (bsum 2 c (2 * 16)) = bsum 4 (fun B => c (2 * B) + c (2 * B + 1)) 16 := by
  rw [pc2, bsum_and (by norm_num) hc hM2, bsum_shr_and (by norm_num) hc hM2]
  exact bsum_add _ _ _ _

theorem pc3_bsum {c : ℕ → ℕ} (hc : ∀ b, c b ≤ 4) (h16 : c 16 = 0) :
    pc3 (bsum 4 c 16) = bsum 8 (fun B => c (2 * B) + c (2 * B + 1)) 8 := by
  have hc' : ∀ b, c b < 2 ^ 4 := fun b => by have := hc b; omega
  have h17 : bsum 4 c (16 + 1) = bsum 4 c 16 := by rw [bsum, h16]; simp
  have hs : bsum 4 c 16 >>> 4 = bsum 4 (fun i => c (i + 1)) 16 := by
    rw [← h17]
    exact bsum_shr (by norm_num) hc' 16
  rw [pc3, hs, bsum_add]
  have hs' : ∀ b, (fun i => c i + c (i + 1)) b < 2 ^ 4 :=
    fun b => by
      have := hc b
      have := hc (b + 1)
      change c b + c (b + 1) < 16
      omega
  exact bsum_and (n := 8) (by norm_num) hs' hM4

theorem pc4_sum (d : ℕ → ℕ) (hd : ∀ b, d b ≤ 8) :
    pc4 (bsum 8 d 8) = ((d 0 + d 1) + (d 2 + d 3)) + ((d 4 + d 5) + (d 6 + d 7)) := by
  have hx : bsum 8 d 8 = d 0 + 256 * d 1 + 65536 * d 2 + 16777216 * d 3 + 4294967296 * d 4 +
      1099511627776 * d 5 + 281474976710656 * d 6 + 72057594037927936 * d 7 := by
    simp only [bsum]
    ring
  have e : (18446744073709551615 : ℕ) = 2 ^ 64 - 1 := by norm_num
  rw [pc4, e, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, hx]
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have h3 := hd 3
  have h4 := hd 4
  have h5 := hd 5
  have h6 := hd 6
  have h7 := hd 7
  have hm : (d 0 + 256 * d 1 + 65536 * d 2 + 16777216 * d 3 + 4294967296 * d 4 +
      1099511627776 * d 5 + 281474976710656 * d 6 + 72057594037927936 * d 7) * 72340172838076673 =
      (d 0 + 256 * (d 0 + d 1) + 65536 * (d 0 + d 1 + d 2) + 16777216 * (d 0 + d 1 + d 2 + d 3) +
        4294967296 * (d 0 + d 1 + d 2 + d 3 + d 4) +
        1099511627776 * (d 0 + d 1 + d 2 + d 3 + d 4 + d 5) +
        281474976710656 * (d 0 + d 1 + d 2 + d 3 + d 4 + d 5 + d 6) +
        72057594037927936 * (d 0 + d 1 + d 2 + d 3 + d 4 + d 5 + d 6 + d 7)) +
      2 ^ 64 * ((d 1 + d 2 + d 3 + d 4 + d 5 + d 6 + d 7) + 256 * (d 2 + d 3 + d 4 + d 5 + d 6 + d 7) +
        65536 * (d 3 + d 4 + d 5 + d 6 + d 7) + 16777216 * (d 4 + d 5 + d 6 + d 7) +
        4294967296 * (d 5 + d 6 + d 7) + 1099511627776 * (d 6 + d 7) + 281474976710656 * d 7) := by
    ring
  rw [hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bits_bsum (m : ℕ) (hm : m < 2 ^ 64) : m = bsum 1 (cnt m 0) (2 * 32) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_bsum (by norm_num) (fun b => by simpa using cnt_lt m 0 b)]
  simp only [Nat.one_mul, Nat.div_one, Nat.mod_one, cnt]
  by_cases hp : p < 64
  · cases m.testBit p <;> simp [hp]
  · have : m.testBit p = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hp' : ¬ p < 2 * 32 := by omega
    simp [hp', this]

public section

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KS.S1277Gm

theorem pcN_eq (m : ℕ) (hm : m < 2 ^ 64) : pcN m = pc64 m := by
  have h1 : pc1 m = bsum 2 (cnt m 1) 32 := by
    conv_lhs => rw [bits_bsum m hm]
    exact pc1_bsum (fun b => by simpa using cnt_lt m 0 b)
  have h2 : pc2 (bsum 2 (cnt m 1) 32) = bsum 4 (cnt m 2) 16 :=
    pc2_bsum (c := cnt m 1) (fun b => lt_of_le_of_lt (cnt_le m 1 b) (by norm_num))
  have h16 : cnt m 2 16 = 0 := by
    have : ∀ j, m.testBit (64 + j) = false := fun j =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [cnt_eq]
    simp [this]
  have h3 : pc3 (bsum 4 (cnt m 2) 16) = bsum 8 (cnt m 3) 8 :=
    pc3_bsum (fun b => cnt_le m 2 b) h16
  have h4 : pc4 (bsum 8 (cnt m 3) 8) = cnt m 6 0 := by
    rw [pc4_sum _ (fun b => cnt_le m 3 b)]
    rfl
  rw [pcN_def, h1, h2, h3, h4, cnt_eq, pc64]
  simp

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem eqB_eq (a b : Bool) : eqB a b = (a == b) := by cases a <;> cases b <;> rfl

theorem strictB_ml (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem allL_eq (f : ℕ → Bool) (l : List ℕ) : allL f l = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change andB (f x) (allL f l) = _
    rw [andB_eq, ih, List.all_cons]

theorem anyL_eq (f : ℕ → Bool) (l : List ℕ) : anyL f l = l.any f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change orB (f x) (anyL f l) = _
    rw [orB_eq, ih, List.any_cons]

theorem filtL_eq (f : ℕ → Bool) (l : List ℕ) : filtL f l = l.filter f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => List ℕ) (filtL f l) (x :: filtL f l) (f x) = _
    rw [ih, List.filter_cons]
    cases f x
    · rfl
    · rfl

theorem cntL_eq (f : ℕ → Bool) (l : List ℕ) : cntL f l = l.countP f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => ℕ) (cntL f l) (Nat.succ (cntL f l)) (f x) = _
    rw [ih, List.countP_cons]
    cases f x
    · rfl
    · rfl

theorem allBelow_true (f : ℕ → Bool) : ∀ n, allBelow f n = true → ∀ c < n, f c = true := by
  intro n
  induction n with
  | zero => intro _ c hc; omega
  | succ n ih =>
    intro h c hc
    change andB (f n) (allBelow f n) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
    · exact ih h.2 c hc
    · exact h.1

theorem testBit_maskF (f : ℕ → ℕ) (l : List ℕ) (x : ℕ) :
    (maskF f l).testBit x = true ↔ ∃ y ∈ l, f y = x := by
  induction l with
  | nil =>
    change (0 : ℕ).testBit x = true ↔ _
    simp
  | cons y l ih =>
    change ((1 <<< f y) ||| maskF f l).testBit x = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih]
    simp

theorem testBit_maskBelow (f : ℕ → Bool) (n x : ℕ) :
    (maskBelow f n).testBit x = (decide (x < n) && f x) := by
  induction n with
  | zero =>
    change (0 : ℕ).testBit x = _
    simp
  | succ n ih =>
    change (Bool.rec (motive := fun _ => ℕ) (maskBelow f n) ((1 <<< n) ||| maskBelow f n)
      (f n)).testBit x = _
    cases h : f n
    · change (maskBelow f n).testBit x = _
      rw [ih]
      by_cases hx : x = n
      · rw [hx, h]
        simp
      · have e : decide (x < n + 1) = decide (x < n) := decide_eq_decide.2 (by omega)
        rw [e]
    · change ((1 <<< n) ||| maskBelow f n).testBit x = _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, ih]
      by_cases hx : x = n
      · rw [hx, h]
        simp
      · have e : decide (x < n + 1) = decide (x < n) := decide_eq_decide.2 (by omega)
        rw [e, decide_eq_false (Ne.symm hx), Bool.false_or]

theorem bitN_eq (m i : ℕ) : bitN m i = m.testBit i := by
  change Nat.blt 0 (m &&& (1 <<< i)) = _
  rw [Nat.one_shiftLeft]
  cases h : m.testBit i
  · have : m &&& 2 ^ i = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : i = j
      · subst hj
        simp [h]
      · simp [hj]
    rw [this]
    rfl
  · have : m &&& 2 ^ i = 2 ^ i := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hj : i = j
      · subst hj
        simp [h]
      · simp [hj]
    rw [this]
    simp only [Nat.blt_eq]
    exact Nat.two_pow_pos i

theorem bitsBelow_eq (m : ℕ) : ∀ n acc,
    bitsBelow m n acc = (List.range n).filter (fun c => m.testBit c) ++ acc := by
  intro n
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
    intro acc
    change bitsBelow m n (Bool.rec (motive := fun _ => List ℕ) acc (n :: acc) (bitN m n)) = _
    rw [bitN_eq, ih, List.range_succ, List.filter_append, List.append_assoc]
    congr 1
    cases h : m.testBit n
    · change acc = _
      simp [h]
    · change n :: acc = _
      simp [h]

theorem land63 (x : ℕ) : Nat.land x (nat_lit 63) = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem land1 (x : ℕ) : Nat.land x (nat_lit 1) = x % 2 := Nat.and_two_pow_sub_one_eq_mod x 1

theorem fldN_eq (p s : ℕ) : fldN p s = (p >>> s) % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6

theorem bit1_eq (v i : ℕ) : bit1 v i = (v >>> i) % 2 := Nat.and_two_pow_sub_one_eq_mod _ 1

theorem appQ_appP (p v : ℕ) : appQ p v = appP p v := by
  unfold appQ
  rw [land63, land1, fldN_eq, fldN_eq, fldN_eq, fldN_eq, fldN_eq, bit1_eq, bit1_eq, bit1_eq,
    bit1_eq, bit1_eq]
  rfl

theorem appQ_eq (p v : ℕ) : appQ p v = (B6.ofP p).app v := by rw [appQ_appP, appP_eq]

theorem appQ_lt (p v : ℕ) : appQ p v < 64 := by rw [appQ_appP]; exact appP_lt p v

theorem testBit_fixMP (p c : ℕ) :
    (fixMP p).testBit c = true ↔ c < 64 ∧ (B6.ofP p).app c = c := by
  change (maskBelow (fun c => Nat.beq (appQ p c) c) 64).testBit c = true ↔ _
  rw [testBit_maskBelow, Bool.and_eq_true, decide_eq_true_iff, Nat.beq_eq, appQ_eq]

theorem lt_of_testBit {x : ℕ} (h : ∀ i, x.testBit i = true → i < 64) : x < 2 ^ 64 :=
  Nat.lt_pow_two_of_testBit x fun i hi => by
    cases e : x.testBit i
    · rfl
    · exact absurd (h i e) (by omega)

theorem fixMP_lt (p : ℕ) : fixMP p < 2 ^ 64 :=
  lt_of_testBit fun i hi => ((testBit_fixMP p i).1 hi).1

theorem fixList_eq (p : ℕ) :
    Certificates.Data.S1277MLine.fixList (B6.ofP p) =
      (List.range 64).filter fun c => (fixMP p).testBit c := by
  rw [Certificates.Data.S1277MLine.fixList]
  apply List.filter_congr
  intro c hc
  have hc' : c < 64 := List.mem_range.1 hc
  apply Bool.eq_iff_iff.2
  rw [testBit_fixMP, beq_iff_eq]
  exact ⟨fun h => ⟨hc', h⟩, fun h => h.2⟩

theorem pcN_fixMP (p : ℕ) :
    pcN (fixMP p) = (Certificates.Data.S1277MLine.fixList (B6.ofP p)).length := by
  rw [pcN_eq _ (fixMP_lt p), fixList_eq, pc64]

theorem imgM_eq (S : List ℕ) (c : ℕ) : imgM S c = maskL (S.map fun p => appP p c) := by
  apply Nat.eq_of_testBit_eq
  intro x
  apply Bool.eq_iff_iff.2
  rw [imgM, testBit_maskF, testBit_maskL]
  simp [appQ_appP, List.mem_map]

theorem maskL_lt (l : List ℕ) (hl : ∀ x ∈ l, x < 64) : maskL l < 2 ^ 64 :=
  lt_of_testBit fun i hi => hl i ((testBit_maskL l i).1 hi)

theorem imgM_lt (S : List ℕ) (c : ℕ) : imgM S c < 2 ^ 64 := by
  rw [imgM_eq]
  refine maskL_lt _ fun x hx => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact appP_lt p c

theorem orbitSize_pcN (S : List ℕ) (c : ℕ) :
    Certificates.Data.S1277MLine.orbitSize (S.map B6.ofP) c = pcN (imgM S c) := by
  have hb : ∀ x ∈ S.map (fun p => appP p c), x < 64 := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact appP_lt p c
  rw [orbitSize_eq_card, map_app, card_eq_pc64 _ hb, pcN_eq _ (imgM_lt S c), imgM_eq]

end

end CFSG.KS.S1277ML
