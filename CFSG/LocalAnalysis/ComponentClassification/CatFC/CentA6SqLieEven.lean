module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrderBig
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)

theorem lieModel_two_card_ne_360 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f) : Nat.card X ≠ 360 := by
  intro hc
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 3) (by rw [hc]; decide)
  rw [hc] at hord
  rcases lie_casework_le (by norm_num) hadm hb with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
  · rcases ht with rfl | rfl <;> revert hord <;> decide
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
      revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem a6sq_sp_ge {q : ℕ} (hq : 2 ≤ q) {r : ℕ} (hr : 3 ≤ r) :
    5760 < q ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1) := by
  induction r, hr using Nat.le_induction with
  | base =>
    have hp : ∏ j ∈ Finset.Icc 1 3, (q ^ (2 * j) - 1) =
        (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) := by
      rw [Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
        Finset.prod_Icc_succ_top (by norm_num)]
      simp
    rw [hp]
    have h1 : 3 ≤ q ^ 2 - 1 := by
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    have h2 : 15 ≤ q ^ 4 - 1 := by
      have : 16 ≤ q ^ 4 := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    have h3 : 63 ≤ q ^ 6 - 1 := by
      have : 64 ≤ q ^ 6 := by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
      omega
    have h4 : 512 ≤ q ^ (3 ^ 2) := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ q ^ 9 := Nat.pow_le_pow_left hq 9
        _ = q ^ (3 ^ 2) := by norm_num
    calc 5760 < 512 * (3 * 15 * 63) := by norm_num
      _ ≤ q ^ (3 ^ 2) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) :=
        Nat.mul_le_mul h4 (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3)
  | succ r hr ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    have h1 : q ^ (r ^ 2) ≤ q ^ ((r + 1) ^ 2) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)
    have h2 : 1 ≤ q ^ (2 * (r + 1)) - 1 := by
      have : 4 ≤ q ^ (2 * (r + 1)) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
          _ ≤ q ^ (2 * (r + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    calc 5760 < q ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1) := ih
      _ ≤ q ^ ((r + 1) ^ 2) * ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1) :=
        Nat.mul_le_mul_right _ h1
      _ = q ^ ((r + 1) ^ 2) * ((∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1)) * 1) := by rw [mul_one]
      _ ≤ q ^ ((r + 1) ^ 2) * ((∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1)) *
          (q ^ (2 * (r + 1)) - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = q ^ ((r + 1) ^ 2) * ((∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1)) *
          (q ^ (2 * (r + 1)) - 1)) := rfl

theorem a6sq_sp_numeric {r g : ℕ} (hr : 1 ≤ r) (hg : 1 ≤ g)
    (hC : (2 ^ g) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((2 ^ g) ^ (2 * j) - 1) ≤ 5760)
    (h360 : 360 ∣ (2 ^ g) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((2 ^ g) ^ (2 * j) - 1)) :
    r = 2 ∧ g = 1 := by
  have hq : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hr2 : r ≤ 2 := by
    by_contra h
    have := a6sq_sp_ge hq (show 3 ≤ r by omega)
    omega
  rcases (by omega : r = 1 ∨ r = 2) with rfl | rfl
  · exfalso
    have hprod : ∏ j ∈ Finset.Icc 1 1, ((2 ^ g) ^ (2 * j) - 1) = (2 ^ g) ^ 2 - 1 := by simp
    rw [hprod] at hC h360
    have hg4 : g ≤ 4 := by
      by_contra h
      have h5 : 32 ≤ 2 ^ g := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h6 : 32 * 1023 ≤ (2 ^ g) ^ (1 ^ 2) * ((2 ^ g) ^ 2 - 1) := by
        have : 1024 ≤ (2 ^ g) ^ 2 := by nlinarith
        rw [one_pow, pow_one]
        exact Nat.mul_le_mul h5 (by omega)
      omega
    interval_cases g <;> revert h360 <;> norm_num
  · refine ⟨rfl, ?_⟩
    by_contra hg1
    have hg2 : 2 ≤ g := by omega
    have hq4 : 4 ≤ 2 ^ g := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
    have hprod : ∏ j ∈ Finset.Icc 1 2, ((2 ^ g) ^ (2 * j) - 1) =
        ((2 ^ g) ^ 2 - 1) * ((2 ^ g) ^ 4 - 1) := by
      rw [Finset.prod_Icc_succ_top (by norm_num)]
      simp
    rw [hprod] at hC
    have h1 : 15 ≤ (2 ^ g) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ g) ^ 2 := by nlinarith
      omega
    have h2 : 255 ≤ (2 ^ g) ^ 4 - 1 := by
      have : 256 ≤ (2 ^ g) ^ 4 := by
        calc 256 = 4 ^ 4 := by norm_num
          _ ≤ (2 ^ g) ^ 4 := Nat.pow_le_pow_left hq4 4
      omega
    have h3 : 256 ≤ (2 ^ g) ^ (2 ^ 2) := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ (2 ^ g) ^ 4 := Nat.pow_le_pow_left hq4 4
        _ = (2 ^ g) ^ (2 ^ 2) := by norm_num
    have h4 : 256 * (15 * 255) ≤ (2 ^ g) ^ (2 ^ 2) * (((2 ^ g) ^ 2 - 1) * ((2 ^ g) ^ 4 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul h1 h2)
    omega

section Data

variable {S : Type} [Group S] [Finite S] {σ : MulAut S}

theorem a6sq_even_data
    (hC : Nat.card (autCentralizer σ) ≤ 5760)
    (hC' : Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6))) :
    ∃ D : Subgroup ↥(fixedSubgroup σ), IsComponent D ∧ IsPComponent 2 D ∧ D.Normal ∧
      Nat.card D = 360 ∧ Nat.card (↥D ⧸ Open.fusionZStar D) = 360 ∧
      360 ∣ Nat.card (fixedSubgroup σ) ∧ Nat.card (fixedSubgroup σ) ≤ 5760 := by
  obtain ⟨e6⟩ := hC'
  obtain ⟨D, hD, hDn, ⟨eD⟩, ⟨eDZ⟩⟩ := a6sq_commutator_component σ e6
  have hDp : IsPComponent 2 D :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hZD : Open.fusionZStar ↥D = center ↥D :=
    fusionZStar_eq_center_of_quasisimple hD.1 (pPrimeCore_ne_top_of_isPComponent hDp)
  refine ⟨D, hD, hDp, hDn, ?_, ?_, a6sq_dvd_card_fixed σ e6, ?_⟩
  · rw [Nat.card_congr eD.toEquiv, a6sq_card]
  · rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZD).toEquiv,
      Nat.card_congr eDZ.toEquiv, a6sq_card]
  · rw [← autCentralizer_eq_fixedSubgroup]; exact hC

end Data

theorem a6sq_close_simple (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    (hX : IsSimpleGroup X) {D : Subgroup X} (hDn : D.Normal) (hD360 : Nat.card D = 360)
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hm : Blueprint.LieModel X t n 2 f) : False := by
  haveI := hX
  haveI := hDn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
  · rw [h] at hD360
    simp at hD360
  · have hcard : Nat.card X = 360 := by rw [← hD360, h, Subgroup.card_top]
    exact lieModel_two_card_ne_360 hO hadm hm hcard

theorem a6sq_close_zstar (hO : LieOrderFormulasInput) {X : Type} [Group X] {D : Subgroup X}
    (hDz : Nat.card (↥D ⧸ Open.fusionZStar D) = 360) {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f)
    (hm : Blueprint.LieModel (↥D ⧸ Open.fusionZStar D) t n 2 f) : False :=
  lieModel_two_card_ne_360 hO hadm hm hDz

theorem lieModel_psu33_card_ne_360 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hm : Blueprint.LieModel X .PSU 3 3 1) : Nat.card X ≠ 360 := by
  intro hc
  have hadm : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  obtain ⟨-, hord, -⟩ := hO X .PSU 3 3 1 hadm hm
  have h1 : lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 := by decide
  have h2 : lieOrderDivisor .PSU 3 (3 ^ 1) = 1 := by decide
  rw [h1, h2, hc] at hord
  omega

end CFSG.ComponentClassification.CatFC
