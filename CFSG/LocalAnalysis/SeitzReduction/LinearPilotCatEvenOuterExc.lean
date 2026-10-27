module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (EvenOuterFamilyExcInput)
open scoped Nat

theorem no_slm_component_of_excInput {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m)
    {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ) {S : Type} [Group S] [Finite S]
    {n e : ℕ} (hadm : StatedLieAdmissible τ n 2 e) (hmS : LieModel S τ n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) : False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S n e hadm hmS σ hσ hout D hP
  have hZ : Open.fusionZStar D = center D :=
    ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hD.1
      (ComponentClassification.CatLeaf.pPrimeCore_ne_top_of_isPComponent hP)
  let E : D ⧸ Open.fusionZStar D ≃* D ⧸ center D := QuotientGroup.quotientMulEquivOfEq hZ
  rcases hX with ⟨τ', e', hτ', hadm', hm'⟩ | hU
  · obtain ⟨rfl, -, -⟩ :=
      hdet (D ⧸ center D) f τ' 0 e' hDm hadm' (LieType.CurtisTits.lieModel_of_mulEquiv E hm')
    exact hτ' (by decide)
  · have hf : 1 ≤ f :=
      (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hDm).1.2.1
    have h1 := GH74.card_of_lieModel_PSU (by norm_num) (by norm_num)
      (LieType.CurtisTits.lieModel_of_mulEquiv E hU)
    rw [card_of_lieModel_PSL_two hDm, show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide]
      at h1
    obtain ⟨hdvd, -, -⟩ := ordA_two_pow_bounds (by omega : 1 ≤ m - 1) hf
    rw [h1] at hdvd
    have hM : f * ((m - 1) * (m - 1 + 1) / 2) ≤ 5 := by
      by_contra hM
      exact absurd ((Nat.pow_dvd_pow 2 (by omega : 6 ≤ _)).trans hdvd) (by decide)
    have hT3 : 3 ≤ (m - 1) * (m - 1 + 1) / 2 := by
      have : 2 * 3 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hf1 : f = 1 := by
      by_contra hne
      have : 2 * 3 ≤ f * ((m - 1) * (m - 1 + 1) / 2) := Nat.mul_le_mul (by omega) hT3
      omega
    subst hf1
    have hm3 : m = 3 := by
      by_contra hne
      have : 3 * 4 ≤ (m - 1) * (m - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    subst hm3
    exact absurd h1 (by decide)

theorem catSLmEvenOuterFamilyAt_of_excInput {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ)
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt τ m :=
  fun _ _ _ _ _ _ _ hadm hmS _ hσ hout _ _ hD hDm _ =>
    (no_slm_component_of_excInput hm hdet h hadm hmS hσ hout hD hDm).elim

theorem catSLmEvenOuterFamilyAt_G2
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .G2 m :=
  catSLmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_G2 hm hdet

theorem catSLmEvenOuterFamilyAt_F4
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .F4 m :=
  catSLmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_F4 hm hdet

theorem catSLmEvenOuterFamilyAt_E6
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .E6 m :=
  catSLmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_E6 hm hdet

theorem catSLmEvenOuterFamilyAt_twistedE6
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .twistedE6 m :=
  catSLmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_twistedE6 hm hdet

theorem catSLmEvenOuterFamilyAt_trialityD4
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .trialityD4 m :=
  catSLmEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_trialityD4 hm hdet

theorem catSLmEvenOuterFamilyAt_E7
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .E7 m :=
  catSLmEvenOuterFamilyAt_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inl rfl)) hm hdet

theorem catSLmEvenOuterFamilyAt_E8
    {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) : CatSLmEvenOuterFamilyAt .E8 m :=
  catSLmEvenOuterFamilyAt_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inr rfl)) hm hdet

end CFSG.SeitzReduction.LinearPilot
