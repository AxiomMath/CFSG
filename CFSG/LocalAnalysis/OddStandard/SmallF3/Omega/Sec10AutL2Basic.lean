module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisBase

public section

namespace CFSG.OddStandard.SmallF3.Omega.AutL2

open CFSG.ComponentClassification.AutL2Facts CFSG.GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

theorem nm_commute_iff (a b : Fˣ) (ε ε' : Bool) (σ τ : F ≃+* F) :
    nm F a ε σ * nm F b ε' τ = nm F b ε' τ * nm F a ε σ ↔
      a * twist F ε (fu F σ b) = b * twist F ε' (fu F τ a) := by
  rw [nm_mul, nm_mul, nm_eq_nm_iff, Bool.xor_comm ε' ε, ringAut_comm τ σ]
  simp

theorem twoVal_eq_four (hH : HarrisHyp F) (hF : Nat.card F = 3 ^ 4) : twoVal F = 4 := by
  refine le_antisymm ?_ hH.four_le
  by_contra h
  push Not at h
  have h3 : 2 ^ 5 ∣ Nat.card F - 1 := (Nat.pow_dvd_pow 2 h).trans (two_pow_twoVal_dvd F)
  rw [hF] at h3
  norm_num at h3

theorem pow_sixteen_of_mem (hH : HarrisHyp F) (hF : Nat.card F = 3 ^ 4) {a : Fˣ}
    (ha : a ∈ zpowers (stdGen F)) : a ^ 16 = 1 := by
  have h := pow_two_pow_twoVal_eq_one ha
  rwa [twoVal_eq_four hH hF] at h

theorem card_ringAut_eq_four (hF : Nat.card F = 3 ^ 4) : Nat.card (F ≃+* F) = 4 :=
  card_ringAut F Nat.prime_three hF

theorem ncard_pow_eq_one_le (n : ℕ) [NeZero n] : {a : Fˣ | a ^ n = 1}.ncard ≤ n := by
  have h : ((rootsOfUnity n F : Subgroup Fˣ) : Set Fˣ) = {a : Fˣ | a ^ n = 1} := by
    ext a
    simp [mem_rootsOfUnity]
  rw [← h, ← Nat.card_coe_set_eq]
  exact card_rootsOfUnity F n

theorem rot_fix_or_inv {a b : Fˣ} {ε : Bool} {σ : F ≃+* F}
    (h : nm F a false 1 * nm F b ε σ = nm F b ε σ * nm F a false 1) :
    fu F σ a = a ∨ fu F σ a = a⁻¹ := by
  rw [nm_commute_iff, fu_one, twist_false] at h
  cases ε
  · left
    rw [twist_false] at h
    exact (mul_left_cancel (a := b) (by rw [mul_comm b, h])).symm
  · right
    rw [twist_true] at h
    have h1 : a = (fu F σ a)⁻¹ := mul_left_cancel (a := b) (by rw [mul_comm b, h])
    exact inv_eq_iff_eq_inv.mp h1.symm

theorem rot_pow_eq_one (hH : HarrisHyp F) (hF : Nat.card F = 3 ^ 4) {a : Fˣ}
    (ha : a ∈ zpowers (stdGen F)) {e : ℕ} {σ : F ≃+* F} (hσ : orderOf σ = 2 ^ e)
    (hfix : fu F σ a = a ∨ fu F σ a = a⁻¹) : a ^ 2 ^ (4 - e) = 1 := by
  have h16 := pow_sixteen_of_mem hH hF ha
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simpa using h16
  have hord : orderOf a ∣ 2 ^ 4 := orderOf_dvd_of_pow_eq_one (by simpa using h16)
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hdvd := two_pow_add_dvd_of_fix_or_inv (p := 3) (f := 4) Nat.prime_three (by norm_num) hF σ
    he hσ a hk hfix
  have hke : k ≤ 4 - e := by
    by_contra hlt
    push Not at hlt
    have h5 : 2 ^ 5 ∣ Nat.card F - 1 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    rw [hF] at h5
    norm_num at h5
  exact orderOf_dvd_iff_pow_eq_one.mp (hk ▸ Nat.pow_dvd_pow 2 hke)

end CFSG.OddStandard.SmallF3.Omega.AutL2
