module

public import CFSG.Certificates.Kernel.LceSP.Base
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

public section

namespace CFSG.Certificates.LceP

open CFSG.KC Finset

@[expose] def gs (X m : ℕ) : ℕ := ∑ t ∈ range m, X ^ t

theorem gs_succ (X m : ℕ) : gs X (m + 1) = gs X m + X ^ m := sum_range_succ _ _

theorem gs_succ' (X m : ℕ) : gs X (m + 1) = 1 + X * gs X m := by
  unfold gs
  rw [sum_range_succ', mul_sum, Nat.add_comm]
  simp [pow_succ']

theorem gs_mul (Y : ℕ) : ∀ m, Y * gs (Y + 1) m + 1 = (Y + 1) ^ m
  | 0 => by simp [gs]
  | m + 1 => by
    rw [gs_succ, mul_add, Nat.add_right_comm, gs_mul Y m]
    ring

theorem gs_shl (Y m k : ℕ) (hY : 0 < Y) (hk : 2 ^ k = (Y + 1) ^ m) :
    Nat.div (Nat.sub (Nat.shiftLeft 1 k) 1) Y = gs (Y + 1) m := by
  change ((1 <<< k) - 1) / Y = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, hk, ← gs_mul Y m, Nat.add_sub_cancel,
    Nat.mul_div_cancel_left _ hY]

theorem shr32 (x k : ℕ) : x >>> (32 * k) = x / (2 ^ 32) ^ k := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]

theorem land_split {a d k : ℕ} (c e : ℕ) (ha : a < 2 ^ k) (hd : d < 2 ^ k) :
    (2 ^ k * c + a) &&& (2 ^ k * e + d) = 2 ^ k * (c &&& e) + (a &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow a hd)]
  split_ifs <;> simp [Nat.testBit_and]

theorem land_maskSum (b : ℕ) : ∀ m x, x &&& ((2 ^ b - 1) * gs (2 ^ (2 * b)) m) =
    ∑ t ∈ range m, (x / 2 ^ (2 * b * t) % 2 ^ b) * 2 ^ (2 * b * t)
  | 0, x => by simp [gs]
  | m + 1, x => by
    have hM : (2 ^ b - 1) * gs (2 ^ (2 * b)) (m + 1) =
        2 ^ (2 * b) * ((2 ^ b - 1) * gs (2 ^ (2 * b)) m) + (2 ^ b - 1) := by
      rw [gs_succ']
      ring
    have hx : x = 2 ^ (2 * b) * (x / 2 ^ (2 * b)) + x % 2 ^ (2 * b) := (Nat.div_add_mod x _).symm
    have hb1 : 2 ^ b - 1 < 2 ^ (2 * b) := by
      have : 2 ^ b ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 0 < 2 ^ b := by positivity
      omega
    rw [hM]
    conv_lhs => rw [hx]
    rw [land_split _ _ (Nat.mod_lt _ (by positivity)) hb1, land_maskSum b m, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), sum_range_succ', mul_sum]
    simp only [Nat.mul_zero, pow_zero, Nat.div_one, Nat.mul_one]
    congr 1
    apply sum_congr rfl
    intro t _
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    have e : 2 * b + 2 * b * t = 2 * b * (t + 1) := by ring
    rw [e]
    ring

@[expose] def ds (b x k : ℕ) : ℕ := ∑ j ∈ range k, x / 2 ^ (b * j) % 2 ^ b

theorem swarMask_eq {b b2 m n : ℕ} (hb : 1 ≤ b) (hb2 : b2 = 2 * b) (hn : n = b2 * m) :
    swarMask n b = (2 ^ b - 1) * gs (2 ^ b2) m := by
  unfold swarMask
  change ((1 <<< n) - 1) / ((1 <<< (2 * b)) - 1) * ((1 <<< b) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, Nat.one_mul]
  have h4 : 0 < 2 ^ (2 * b) - 1 := by
    have : 2 ^ 1 ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hY : 2 ^ (2 * b) - 1 + 1 = 2 ^ (2 * b) := by omega
  have key : (2 ^ (2 * b)) ^ m - 1 = (2 ^ (2 * b) - 1) * gs (2 ^ (2 * b)) m := by
    have := gs_mul (2 ^ (2 * b) - 1) m
    rw [hY] at this
    omega
  have e2 : 2 ^ n = (2 ^ (2 * b)) ^ m := by rw [hn, hb2, pow_mul]
  rw [e2, key, Nat.mul_div_cancel_left _ h4, Nat.mul_comm, hb2]

theorem sum_pairs (f : ℕ → ℕ) : ∀ m, ∑ t ∈ range m, (f (2 * t) + f (2 * t + 1)) =
    ∑ j ∈ range (2 * m), f j
  | 0 => rfl
  | m + 1 => by
    rw [sum_range_succ, sum_pairs f m, Nat.mul_succ, sum_range_succ, sum_range_succ, Nat.add_assoc]

theorem swarStep_rep {b b2 m n : ℕ} (hb : 1 ≤ b) (hb2 : b2 = 2 * b) (hn : n = b2 * m) (x : ℕ) :
    swarStep n b x = ∑ t ∈ range m,
      (x / 2 ^ (b * (2 * t)) % 2 ^ b + x / 2 ^ (b * (2 * t + 1)) % 2 ^ b) * (2 ^ b2) ^ t := by
  unfold swarStep
  rw [swarMask_eq hb hb2 hn]
  change (x &&& _) + ((x >>> b) &&& _) = _
  rw [hb2, land_maskSum, land_maskSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add, ← pow_mul, add_mul]
  have e1 : 2 * b * t = b * (2 * t) := by ring
  have e2 : b + 2 * b * t = b * (2 * t + 1) := by ring
  rw [e2, e1]

theorem digit_sum {B : ℕ} (hB : 0 < B) : ∀ m (e : ℕ → ℕ), (∀ t < m, e t < B) → ∀ s < m,
    (∑ t ∈ range m, e t * B ^ t) / B ^ s % B = e s
  | 0, _, _, s, hs => absurd hs (Nat.not_lt_zero s)
  | m + 1, e, he, s, hs => by
    have hsplit : ∑ t ∈ range (m + 1), e t * B ^ t =
        B * ∑ t ∈ range m, e (t + 1) * B ^ t + e 0 := by
      rw [sum_range_succ', mul_sum]
      simp only [pow_zero, Nat.mul_one, pow_succ]
      congr 1
      apply sum_congr rfl
      intro t _
      ring
    rw [hsplit]
    have he0 := he 0 (by omega)
    rcases s with _ | s
    · simp only [pow_zero, Nat.div_one]
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt he0
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.mul_add_div hB, Nat.div_eq_of_lt he0,
        Nat.add_zero]
      exact digit_sum hB m (fun t => e (t + 1)) (fun t ht => he (t + 1) (by omega)) s (by omega)

theorem ds_swarStep {b b2 m m2 n : ℕ} (hb : 1 ≤ b) (hb2 : b2 = 2 * b) (hn : n = b2 * m)
    (hm2 : m2 = 2 * m) (x : ℕ) : ds b2 (swarStep n b x) m = ds b x m2 := by
  unfold ds
  rw [hm2, ← sum_pairs]
  apply sum_congr rfl
  intro s hs
  rw [Finset.mem_range] at hs
  rw [pow_mul, swarStep_rep hb hb2 hn x]
  rw [digit_sum (by positivity) m _ ?_ s hs]
  intro t _
  have h1 : x / 2 ^ (b * (2 * t)) % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  have h2 : x / 2 ^ (b * (2 * t + 1)) % 2 ^ b < 2 ^ b := Nat.mod_lt _ (by positivity)
  have h3 : 2 ^ b * 2 ≤ 2 ^ b2 := by
    rw [hb2, ← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem mul_gs (X : ℕ) : ∀ m (e : ℕ → ℕ), ∃ Lw Hh,
    (∑ t ∈ range (m + 1), e t * X ^ t) * gs X (m + 1) =
      Lw + X ^ m * (∑ t ∈ range (m + 1), e t) + X ^ (m + 1) * Hh ∧
    Lw ≤ (∑ t ∈ range (m + 1), e t) * gs X m
  | 0, e => ⟨0, 0, by simp [gs], by simp⟩
  | m + 1, e => by
    obtain ⟨L', H', h1, h2⟩ := mul_gs X m (fun t => e (t + 1))
    have hY : ∑ t ∈ range (m + 1 + 1), e t * X ^ t =
        X * ∑ t ∈ range (m + 1), e (t + 1) * X ^ t + e 0 := by
      rw [sum_range_succ', mul_sum]
      simp only [pow_zero, Nat.mul_one, pow_succ]
      congr 1
      apply sum_congr rfl
      intro t _
      ring
    have hT : ∑ t ∈ range (m + 1 + 1), e t = ∑ t ∈ range (m + 1), e (t + 1) + e 0 :=
      sum_range_succ' _ _
    refine ⟨e 0 * gs X (m + 1) + X * L', H' + ∑ t ∈ range (m + 1), e (t + 1) * X ^ t, ?_, ?_⟩
    · rw [hY, hT, gs_succ X (m + 1)]
      have : (X * ∑ t ∈ range (m + 1), e (t + 1) * X ^ t + e 0) *
          (gs X (m + 1) + X ^ (m + 1)) =
          X * ((∑ t ∈ range (m + 1), e (t + 1) * X ^ t) * gs X (m + 1)) +
          e 0 * gs X (m + 1) + e 0 * X ^ (m + 1) +
          X ^ (m + 1 + 1) * ∑ t ∈ range (m + 1), e (t + 1) * X ^ t := by ring
      rw [this, h1]
      ring
    · rw [hT]
      have h3 : X * gs X m ≤ gs X (m + 1) := by rw [gs_succ']; omega
      calc e 0 * gs X (m + 1) + X * L'
          ≤ e 0 * gs X (m + 1) + X * ((∑ t ∈ range (m + 1), e (t + 1)) * gs X m) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
        _ = e 0 * gs X (m + 1) + (∑ t ∈ range (m + 1), e (t + 1)) * (X * gs X m) := by ring
        _ ≤ e 0 * gs X (m + 1) + (∑ t ∈ range (m + 1), e (t + 1)) * gs X (m + 1) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ h3) _
        _ = (∑ t ∈ range (m + 1), e (t + 1) + e 0) * gs X (m + 1) := by ring

theorem ds_one (x k : ℕ) : ds 1 x k = ∑ j ∈ range k, x / 2 ^ j % 2 := by
  simp [ds]

theorem ds_one_le (x k : ℕ) : ds 1 x k ≤ k := by
  rw [ds_one]
  calc ∑ j ∈ range k, x / 2 ^ j % 2 ≤ ∑ _j ∈ range k, 1 :=
        sum_le_sum fun j _ => by have := Nat.mod_lt (x / 2 ^ j) (by norm_num : 0 < 2); omega
    _ = k := by simp

theorem pc4096_eq (x : ℕ) : pc4096 x = ∑ j ∈ range 4096, x / 2 ^ j % 2 := by
  set x1 := swarStep 4096 1 x
  set x2 := swarStep 4096 2 x1
  set x3 := swarStep 4096 4 x2
  set x4 := swarStep 4096 8 x3
  have c1 : ds 2 x1 2048 = ds 1 x 4096 :=
    ds_swarStep (b := 1) (b2 := 2) (m := 2048) (m2 := 4096) (n := 4096) (by norm_num) rfl rfl rfl x
  have c2 : ds 4 x2 1024 = ds 2 x1 2048 :=
    ds_swarStep (b := 2) (b2 := 4) (m := 1024) (m2 := 2048) (n := 4096) (by norm_num) rfl rfl rfl x1
  have c3 : ds 8 x3 512 = ds 4 x2 1024 :=
    ds_swarStep (b := 4) (b2 := 8) (m := 512) (m2 := 1024) (n := 4096) (by norm_num) rfl rfl rfl x2
  have c4 : ds 16 x4 256 = ds 8 x3 512 :=
    ds_swarStep (b := 8) (b2 := 16) (m := 256) (m2 := 512) (n := 4096) (by norm_num) rfl rfl rfl x3
  have hrep := swarStep_rep (b := 16) (b2 := 32) (m := 128) (n := 4096) (by norm_num) rfl rfl x4
  set e : ℕ → ℕ := fun t => x4 / 2 ^ (16 * (2 * t)) % 2 ^ 16 + x4 / 2 ^ (16 * (2 * t + 1)) % 2 ^ 16
  have hT : ∑ t ∈ range (127 + 1), e t = ds 1 x 4096 := by
    rw [← c1, ← c2, ← c3, ← c4]
    unfold ds
    exact sum_pairs (fun j => x4 / 2 ^ (16 * j) % 2 ^ 16) 128
  have hTle : ∑ t ∈ range (127 + 1), e t ≤ 4096 := by
    rw [hT]
    exact ds_one_le x 4096
  obtain ⟨Lw, Hh, hm, hL⟩ := mul_gs (2 ^ 32) 127 e
  have h3 : (2 : ℕ) ^ 32 = 4294967295 + 1 := by norm_num
  have hG : Nat.div (Nat.sub (Nat.shiftLeft 1 4096) 1) 4294967295 = gs (2 ^ 32) 128 := by
    rw [h3]
    exact gs_shl 4294967295 128 4096 (by norm_num) (by rw [← h3, ← pow_mul])
  have hLw : Lw < (2 ^ 32) ^ 127 := by
    have h1 := gs_mul 4294967295 127
    have h2 : Lw ≤ 4294967295 * gs (2 ^ 32) 127 :=
      le_trans hL (Nat.mul_le_mul_right _ (by omega))
    rw [h3] at h2 ⊢
    omega
  change Nat.land (Nat.shiftRight (Nat.mul (swarStep 4096 16 x4)
    (Nat.div (Nat.sub (Nat.shiftLeft 1 4096) 1) 4294967295)) (Nat.sub 4096 32)) 4294967295 = _
  rw [hG]
  change (swarStep 4096 16 x4 * gs (2 ^ 32) 128) >>> (32 * 127) &&& (2 ^ 32 - 1) = _
  rw [hrep, Nat.and_two_pow_sub_one_eq_mod, shr32]
  change (∑ t ∈ range (127 + 1), e t * (2 ^ 32) ^ t) * gs (2 ^ 32) (127 + 1) / (2 ^ 32) ^ 127 %
    2 ^ 32 = _
  rw [hm]
  have e2 : Lw + (2 ^ 32) ^ 127 * (∑ t ∈ range (127 + 1), e t) + (2 ^ 32) ^ (127 + 1) * Hh =
      Lw + (2 ^ 32) ^ 127 * ((∑ t ∈ range (127 + 1), e t) + 2 ^ 32 * Hh) := by ring
  have hpos : 0 < (2 ^ 32 : ℕ) ^ 127 := by positivity
  rw [e2]
  rw [Nat.add_mul_div_left _ _ hpos]
  rw [Nat.div_eq_of_lt hLw, Nat.zero_add]
  rw [Nat.add_mul_mod_self_left]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hTle (by norm_num)), hT, ds_one]

end CFSG.Certificates.LceP

end
