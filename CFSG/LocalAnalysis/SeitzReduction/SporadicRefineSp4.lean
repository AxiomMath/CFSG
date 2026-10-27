module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatSporadicFour
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem card_quotient_center_sp4_four {X : Type} [Group X] {D : Subgroup X} (hD : IsComponent D)
    (hDm : LieModel D .PSp 2 2 2) : Nat.card (D ⧸ center D) = 979200 := by
  rw [SymplecticPilot.card_quotient_center_of_lieModel_PSp hD hDm,
    SymplecticPilot.ordBC_two_two_eq]

theorem card_quotient_center_sp4_eight {X : Type} [Group X] {D : Subgroup X} (hD : IsComponent D)
    (hDm : LieModel D .PSp 2 2 3) : Nat.card (D ⧸ center D) = 1056706560 := by
  rw [SymplecticPilot.card_quotient_center_of_lieModel_PSp hD hDm,
    SymplecticPilot.ordBC_two_three_eq]

theorem card_quotient_center_sp4_four_or_eight {X : Type} [Group X] {D : Subgroup X}
    (hD : IsComponent D) {f : ℕ} (hf : f = 2 ∨ f = 3) (hDm : LieModel D .PSp 2 2 f) :
    Nat.card (D ⧸ center D) = 979200 ∨ Nat.card (D ⧸ center D) = 1056706560 := by
  rcases hf with rfl | rfl
  · exact .inl (card_quotient_center_sp4_four hD hDm)
  · exact .inr (card_quotient_center_sp4_eight hD hDm)

section He


theorem he_false_of_not_dvd {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.He) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : ¬ Nat.card (D ⧸ center D) ∣ 15120)
    (hσD : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
      FixedCentralizerTwoFree σ D) : False := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs : orderOf s = 2 := by
      rw [← orderOf_injective _
        (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna) s]
      exact hσ
    rcases hσD with ⟨-, hsmall⟩ | hfree
    · exact he_inner_not_twoSmall e hs hD hsmall
    · exact LinearPilot.not_mem_range_conj_of_twoFree hna hσ hfree ⟨s, rfl⟩
  · have h := card_quotient_center_dvd_card_fixedSubgroup D
    rw [he_outer_card_fixedSubgroup e hσ hin] at h
    exact hcard h

theorem sp4_false_of_he {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.He) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel D .PSp 2 2 2)
    (hσD : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
      FixedCentralizerTwoFree σ D) : False :=
  he_false_of_not_dvd hS hna e hσ hD (by rw [card_quotient_center_sp4_four hD hDm]; norm_num) hσD

end He

section Fi23


theorem sp4_false_of_fi23 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {f : ℕ} (hf : f = 2 ∨ f = 3) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel D .PSp 2 2 f) : False := by
  have h := OmegaPilot.fi23_eleven_dvd_card_quotient_center hS hna e hσ hD
  rcases card_quotient_center_sp4_four_or_eight hD hf hDm with hc | hc <;> rw [hc] at h <;> omega

end Fi23

section Fi24


theorem sp4_false_of_fi24 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi24Prime)
    {σ : MulAut S} (hσ : orderOf σ = 2) {f : ℕ} (hf : f = 2 ∨ f = 3)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hDm : LieModel D .PSp 2 2 f) :
    False := by
  have h := OmegaPilot.fi24_card_quotient_center hS hna e hσ hD
  rcases card_quotient_center_sp4_four_or_eight hD hf hDm with hc | hc <;> rw [hc] at h <;> omega

end Fi24

section Baby


theorem sp4_false_of_baby {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .B) {σ : MulAut S}
    (hσ : orderOf σ = 2) {f : ℕ} (hf : f = 2 ∨ f = 3) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel D .PSp 2 2 f) : False := by
  have h := OmegaPilot.baby_card_quotient_center hS hna e hσ hD
  rcases card_quotient_center_sp4_four_or_eight hD hf hDm with hc | hc <;> rw [hc] at h <;> omega

end Baby

section Co1


theorem sp4_false_of_co1 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co1) {σ : MulAut S}
    (hσ : orderOf σ = 2) {f : ℕ} (hf : f = 2 ∨ f = 3) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel D .PSp 2 2 f) : False := by
  have hc := card_quotient_center_sp4_four_or_eight hD hf hDm
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Co1 σ
  obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
  have h := (ComponentClassification.RestrictedStd.Spor.co1LocalComponentsInput_holds S e u
    (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB).1
  rw [hcard] at h
  omega

end Co1

end CFSG.SeitzReduction.SporadicRefine
