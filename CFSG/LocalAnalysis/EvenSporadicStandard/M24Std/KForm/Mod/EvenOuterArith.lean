module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrderBig
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem lieModel_two_not_a6data (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f) (h360 : 360 ∣ Nat.card X)
    (h64 : ¬ 2 ^ 6 ∣ Nat.card X) : False := by
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 5) h64
  have hN : 360 ∣ lieOrderNumerator t n (2 ^ f) := by
    rw [← hord]
    exact h360.mul_right _
  rcases lie_casework_le (by norm_num) hadm hb with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, rfl⟩ |
      ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;>
      first | exact absurd rfl hadm.2.2.2 | (revert hN; decide)
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;>
      first | exact absurd rfl hadm.2.2.2 | (revert hN; decide)
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;> norm_num at hb
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
      exact absurd hadm.2.2.2.2.2 (by omega)

theorem sp_fixed_two_part {X : Type} [Group X] {k : Type} [Field k] [Finite k] {r g : ℕ}
    (hk : Nat.card k = 2 ^ g) (hr : 1 ≤ r) (hg : 1 ≤ g) (Φ : X ≃* StatedSp r k)
    (h360 : 360 ∣ Nat.card X) (h64 : ¬ 2 ^ 6 ∣ Nat.card X) : r = 2 ∧ g = 1 := by
  have hc : Nat.card X =
      (2 ^ g) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((2 ^ g) ^ (2 * j) - 1) := by
    rw [Nat.card_congr Φ.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk]
  rw [hc] at h360 h64
  have hle : g * r ^ 2 ≤ 5 := by
    by_contra h
    have h6 : 6 ≤ g * r ^ 2 := by omega
    have hdvd : 2 ^ 6 ∣ (2 ^ g) ^ (r ^ 2) := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 h6
    exact h64 (hdvd.trans (dvd_mul_right _ _))
  have hr2 : r ≤ 2 := by
    by_contra h
    have hr3 : 3 ≤ r := by omega
    have h9 : 9 ≤ r ^ 2 := by simpa using Nat.pow_le_pow_left hr3 2
    have h6 : 6 ≤ g * r ^ 2 := by
      calc 6 ≤ 9 := by norm_num
        _ ≤ g * r ^ 2 := by simpa using Nat.mul_le_mul hg h9
    exact absurd (le_trans h6 hle) (by norm_num)
  rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
  · exfalso
    have hprod : ∏ j ∈ Finset.Icc 1 1, ((2 ^ g) ^ (2 * j) - 1) = (2 ^ g) ^ 2 - 1 := by simp
    rw [hprod] at h360
    have hg5 : g ≤ 5 := by simpa using hle
    interval_cases g <;> revert h360 <;> norm_num
  · refine ⟨rfl, ?_⟩
    have hg1 : g ≤ 1 := by
      have : g * 4 ≤ 5 := by simpa using hle
      omega
    omega

theorem lieModel_psu33_not_dvd (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hm : Blueprint.LieModel X .PSU 3 3 1) (h360 : 360 ∣ Nat.card X) : False := by
  have hadm : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  obtain ⟨-, hord, -⟩ := hO X .PSU 3 3 1 hadm hm
  have h1 : lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 := by decide
  have h2 : lieOrderDivisor .PSU 3 (3 ^ 1) = 1 := by decide
  rw [h1, h2, mul_one] at hord
  rw [hord] at h360
  norm_num at h360

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
