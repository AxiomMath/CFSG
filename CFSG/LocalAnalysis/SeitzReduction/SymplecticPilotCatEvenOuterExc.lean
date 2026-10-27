module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuterClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (EvenOuterFamilyExcInput)


theorem no_sp2m_component_of_excInput {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ)
    {S : Type} [Group S] [Finite S] {n e : ℕ} (hadm : StatedLieAdmissible τ n 2 e)
    (hmS : LieModel S τ n 2 e) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {m f : ℕ}
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hDm : LieModel D .PSp m 2 f) :
    False := by
  have hP := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  have hX := h S n e hadm hmS σ hσ hout D hP
  have : IsSimpleGroup D := F4Pilot.isSimpleGroup_of_lieModel_PSp hDm
  obtain ⟨E⟩ :=
    ComponentClassification.GrSLit.nonempty_fusionZStar_equiv_of_simple hP (MulEquiv.refl D)
  rcases hX with ⟨τ', e', hτ', hadm', hm'⟩ | hU
  · obtain ⟨rfl, -, -⟩ :=
      sp2mEvenTypeDet m D f τ' 0 e' hDm hadm' (LieType.CurtisTits.lieModel_of_mulEquiv E hm')
    exact hτ' (by decide)
  · have h1 := GH74.card_of_lieModel_PSU (by norm_num) (by norm_num)
      (LieType.CurtisTits.lieModel_of_mulEquiv E hU)
    rw [show Open.ordTwistedA (3 - 1) (3 ^ 1) = 6048 by decide] at h1
    have h8 := two_pow_eight_dvd_card_of_lieModel_PSp hDm
    rw [h1] at h8
    exact absurd h8 (by decide)

theorem catSp2mEvenOuterFamily_of_excInput {τ : StatedLieTag} (h : EvenOuterFamilyExcInput τ)
    (m : ℕ) : CatSp2mEvenOuterFamily τ m :=
  fun _ _ _ _ _ _ _ hadm hmS _ hσ hout _ _ hD hDm =>
    (no_sp2m_component_of_excInput h hadm hmS hσ hout hD hDm).elim

theorem catSp2mEvenOuterFamily_G2
    (m : ℕ) : CatSp2mEvenOuterFamily .G2 m :=
  catSp2mEvenOuterFamily_of_excInput F4Pilot.evenOuterFamilyExcInput_G2 m

theorem catSp2mEvenOuterFamily_F4
    (m : ℕ) : CatSp2mEvenOuterFamily .F4 m :=
  catSp2mEvenOuterFamily_of_excInput F4Pilot.evenOuterFamilyExcInput_F4 m

theorem catSp2mEvenOuterFamily_E6
    (m : ℕ) : CatSp2mEvenOuterFamily .E6 m :=
  catSp2mEvenOuterFamily_of_excInput F4Pilot.evenOuterFamilyExcInput_E6 m

theorem catSp2mEvenOuterFamily_E7
    (m : ℕ) : CatSp2mEvenOuterFamily .E7 m :=
  catSp2mEvenOuterFamily_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inl rfl)) m

theorem catSp2mEvenOuterFamily_E8
    (m : ℕ) : CatSp2mEvenOuterFamily .E8 m :=
  catSp2mEvenOuterFamily_of_excInput (F4Pilot.evenOuterFamilyExcInput_E7_E8 (Or.inr rfl)) m

theorem catSp2mEvenOuterFamily_twistedE6
    (m : ℕ) : CatSp2mEvenOuterFamily .twistedE6 m :=
  catSp2mEvenOuterFamily_of_excInput F4Pilot.evenOuterFamilyExcInput_twistedE6 m

theorem catSp2mEvenOuterFamily_trialityD4 (m : ℕ) : CatSp2mEvenOuterFamily .trialityD4 m :=
  catSp2mEvenOuterFamily_of_excInput F4Pilot.evenOuterFamilyExcInput_trialityD4 m

end CFSG.SeitzReduction.SymplecticPilot
