module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECU62
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOmega

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

theorem noOddPSL2_O82 {J : Type} [Group J] (hm : Blueprint.LieModel J .POmegaPlus 4 2 1) :
    NoOddPSL2 J := by
  intro α hα hαo P hP p m hp2 hL
  have hadm : StatedLieAdmissible .POmegaPlus 4 2 1 := admissible_of_lieModel hm
  have : Finite J := by
    obtain ⟨K, _, _, Q, -, -, -, -, -, ⟨e⟩⟩ := EvenOrthSelector.exists_coordinate_witness
      (Or.inl rfl) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm)
    exact Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨K, _, _, hK, hch | ⟨⟨Φ⟩⟩ | ⟨⟨σ, hσ⟩, -⟩⟩ :=
    evenOrthogonal_outer_fixed_cases (Or.inl rfl) hadm hm α hα hαo
  · exact not_isPComponent_of_isCharacteristicP hch P hP
  · exact not_psl2_of_statedSp_three (by rw [hK, pow_one]) Φ hP hp2 hL
  · exact hσ (ringEquiv_eq_one_of_card_two (by rw [hK, pow_one]) σ)

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
