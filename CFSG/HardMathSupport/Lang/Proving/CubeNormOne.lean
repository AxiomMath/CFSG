module

public import CFSG.HardMathSupport.Lang.Proving.CubeClassField
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.HardMathSupport.Lang.Proving

theorem pow_three_mul_succ_eq_self {M : Type*} [Monoid M] {a : M} (ha : a ^ 3 = 1) (s : ℕ) :
    a ^ (3 * s + 1) = a := by
  rw [pow_succ, pow_mul, ha, one_pow, one_mul]

theorem sq_sub_one_eq_three_mul {q c : ℕ} (hc : q + 1 = 3 * c) :
    q ^ 2 - 1 = 3 * ((q - 1) * c) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
  have h' : (r + 2) ^ 2 = (r + 1) * (r + 3) + 1 := by ring
  rw [h', Nat.add_sub_cancel, show r + 2 - 1 = r + 1 by omega, show r + 3 = 3 * c by omega]
  ring

theorem exists_cube_val_iff {K : Type*} [Field K] (L : Kˣ) :
    (∃ x : K, x ^ 3 = (L : K)) ↔ ∃ y : Kˣ, y ^ 3 = L := by
  constructor
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply L.ne_zero
      rw [← hx]
      simp
    exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx)⟩
  · rintro ⟨y, hy⟩
    exact ⟨(y : K), by rw [← Units.val_pow_eq_pow_val, hy]⟩

theorem cube_normOne_iff {K : Type*} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) {l : K} (hl : l ^ (q + 1) = 1) :
    ((∃ x : K, x ^ 3 = l) ↔ l ^ ((q + 1) / 3) = 1) ∧
      ((∃ x : K, x ^ 3 = l) → ∃ x : K, x ^ (q + 1) = 1 ∧ x ^ 3 = l) := by
  obtain ⟨c, hc⟩ := h3
  have hc1 : (q + 1) / 3 = c := by omega
  have hq1 : q - 1 = 3 * (c - 1) + 1 := by omega
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hl
    exact zero_ne_one hl
  obtain ⟨L, hL⟩ : ∃ L : Kˣ, (L : K) = l := ⟨Units.mk0 l hl0, rfl⟩
  have hLq : L ^ (q + 1) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hL, Units.val_one]; exact hl)
  have hexp : (Nat.card K - 1) / 3 = (q - 1) * c := by
    rw [hK, sq_sub_one_eq_three_mul hc, Nat.mul_div_cancel_left _ (by norm_num)]
  have h3K : 3 ∣ Nat.card K - 1 := ⟨(q - 1) * c, by rw [hK, sq_sub_one_eq_three_mul hc]⟩
  have hU3 : (L ^ c) ^ 3 = 1 := by
    rw [← pow_mul, show c * 3 = q + 1 by omega]
    exact hLq
  have hcube : (∃ x : K, x ^ 3 = l) ↔ L ^ c = 1 := by
    rw [← hL, exists_cube_val_iff, exists_cube_iff_pow_eq_one h3K L, hexp, mul_comm (q - 1) c,
      pow_mul, hq1, pow_three_mul_succ_eq_self hU3]
  refine ⟨?_, ?_⟩
  · rw [hcube, hc1, ← hL, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply hl0
      rw [← hx]
      simp
    obtain ⟨X, hX⟩ : ∃ X : Kˣ, (X : K) = x := ⟨Units.mk0 x hx0, rfl⟩
    have hX3 : X ^ 3 = L := Units.ext (by rw [Units.val_pow_eq_pow_val, hX, hL, hx])
    have hmul : (q + 1) * (q - 1) = 3 * ((q - 1) * c) := by
      rw [hc]
      ring
    have hcardU : Nat.card Kˣ = (q + 1) * (q - 1) := by
      rw [hmul, Nat.card_units, hK, sq_sub_one_eq_three_mul hc]
    have hLagrange : X ^ ((q + 1) * (q - 1)) = 1 := by
      classical
      have : Fintype K := Fintype.ofFinite K
      rw [← hcardU, Nat.card_eq_fintype_card]
      exact pow_card_eq_one
    have hY3 : (X ^ (q + 1)) ^ 3 = 1 := by
      rw [pow_right_comm, hX3, hLq]
    have hYq : (X ^ (q + 1)) ^ (q - 1) = 1 := by
      rw [← pow_mul]
      exact hLagrange
    have hY : X ^ (q + 1) = 1 := by
      have h1 := pow_three_mul_succ_eq_self hY3 (c - 1)
      rw [← hq1, hYq] at h1
      exact h1.symm
    refine ⟨x, ?_, hx⟩
    rw [← hX, ← Units.val_pow_eq_pow_val, hY, Units.val_one]

theorem exists_primitive_cube_root_normOne {K : Type*} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ (q + 1) = 1 ∧ ω ^ q = ω⁻¹ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := h3
  have hdvd : 3 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hK, sq_sub_one_eq_three_mul hc]
    exact dvd_mul_right 3 _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    norm_num at hx
  have hxq : x ^ (q + 1) = 1 := by
    rw [hc, pow_mul, hx3, one_pow]
  have hxq' : x ^ q = x⁻¹ := by
    rw [pow_succ] at hxq
    exact eq_inv_of_mul_eq_one_left hxq
  refine ⟨(x : K), ?_, ?_, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, hx3, Units.val_one]
  · intro h
    exact hx1 (Units.val_eq_one.mp h)
  · rw [← Units.val_pow_eq_pow_val, hxq, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, hxq', Units.val_inv_eq_inv_val]

theorem cube_units_iff {K : Type*} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q)
    (h3 : 3 ∣ q - 1) {l : K} (hl : l ≠ 0) :
    (∃ x : K, x ^ 3 = l) ↔ l ^ ((q - 1) / 3) = 1 := by
  obtain ⟨L, hL⟩ : ∃ L : Kˣ, (L : K) = l := ⟨Units.mk0 l hl, rfl⟩
  have h3K : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  have hexp : (Nat.card K - 1) / 3 = (q - 1) / 3 := by rw [hK]
  rw [← hL, exists_cube_val_iff, exists_cube_iff_pow_eq_one h3K L, hexp,
    ← Units.val_pow_eq_pow_val, Units.val_eq_one]

end CFSG.HardMathSupport.Lang.Proving

end
