module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenOuter
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (EvenOuterFamilyExcInput)

theorem no_omega_component_of_excInput {m : ℕ} (hdet : OmegaEvenTypeDetAt m) {τ : StatedLieTag}
    (h : EvenOuterFamilyExcInput τ) {S : Type} [Group S] [Finite S] {n e : ℕ}
    (hadm : StatedLieAdmissible τ n 2 e) (hmS : LieModel S τ n 2 e) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {f : ℕ} {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) t m 2 f) : False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S n e hadm hmS σ hσ hout D hP
  have hZ : Open.fusionZStar D = center D :=
    ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hD.1
      (ComponentClassification.CatLeaf.pPrimeCore_ne_top_of_isPComponent hP)
  let E : D ⧸ Open.fusionZStar D ≃* D ⧸ center D := QuotientGroup.quotientMulEquivOfEq hZ
  rcases hX with ⟨τ', e', hτ', hadm', hm'⟩ | hU
  · obtain ⟨-, h0, -⟩ :=
      hdet (D ⧸ center D) t f τ' 0 e' ht hDm hadm' (LieType.CurtisTits.lieModel_of_mulEquiv E hm')
    have := four_le_of_lieModel_POmega ht hDm
    omega
  · have h1 := GH74.card_of_lieModel_PSU (by norm_num) (by norm_num)
      (LieType.CurtisTits.lieModel_of_mulEquiv E hU)
    rw [show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide] at h1
    have h12 := two_pow_twelve_dvd_card_of_lieModel_POmega ht hDm
    rw [h1] at h12
    exact absurd h12 (by decide)

theorem catOmegaEvenOuterFamilyAt_of_excInput {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ)
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) : CatOmegaEvenOuterFamilyAt τ m :=
  fun _ _ _ _ _ _ _ hadm hmS _ hσ hout _ _ _ ht hD hDm _ =>
    (no_omega_component_of_excInput hdet h hadm hmS hσ hout ht hD hDm).elim

section Exceptional

theorem catOmegaEvenOuterFamilyAt_G2
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .G2 m :=
  catOmegaEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_G2 hdet

theorem catOmegaEvenOuterFamilyAt_F4
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .F4 m :=
  catOmegaEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_F4 hdet

theorem catOmegaEvenOuterFamilyAt_E6
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .E6 m :=
  catOmegaEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_E6 hdet

theorem catOmegaEvenOuterFamilyAt_twistedE6
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .twistedE6 m :=
  catOmegaEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_twistedE6 hdet

theorem catOmegaEvenOuterFamilyAt_trialityD4
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .trialityD4 m :=
  catOmegaEvenOuterFamilyAt_of_excInput F4Pilot.evenOuterFamilyExcInput_trialityD4 hdet

theorem catOmegaEvenOuterFamilyAt_E7
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .E7 m :=
  catOmegaEvenOuterFamilyAt_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inl rfl)) hdet

theorem catOmegaEvenOuterFamilyAt_E8
    {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterFamilyAt .E8 m :=
  catOmegaEvenOuterFamilyAt_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inr rfl)) hdet

end Exceptional

end CFSG.SeitzReduction.OmegaPilot
