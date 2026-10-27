module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Omega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6OmegaInner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6Split

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

theorem oddLieA6CentreFor_POmegaOdd
    : OddLieA6CentreFor .POmegaOdd := by
  intro J _ n p f hp hp2 hadm hm α hα
  have hC : StatedClassicalModel J .POmegaOdd n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl)
    (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  refine a6CentreForm_of_semilinearRepresentation hrep (coordinateOddWitnessEquiv K e)
    (fun g hσ2 hord => ?_) α hα
  by_cases hσ : g.val.right = 1
  · exact a6_omegaOdd_linear n K p f hp hp2 hK hadm g hσ hord
  · exact a6_omegaOdd_field n K p f hp hp2 hK hadm g hσ2 hσ hord

theorem oddLieA6CentreFor_POmegaPlus
    : OddLieA6CentreFor .POmegaPlus := by
  intro J _ n p f hp hp2 hadm hm α hα
  have hC : StatedClassicalModel J .POmegaPlus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) K hK e
  refine a6CentreForm_of_semilinearRepresentation hrep (coordinatePlusWitnessEquiv K e)
    (fun g hσ2 hord => ?_) α hα
  by_cases hσ : g.val.right = 1
  · exact a6_omegaPlus_linear n K p f hp hp2 hK hadm g hσ hord
  · exact a6_omegaPlus_field n K p f hp hp2 hK hadm g hσ2 hσ hord

theorem oddLieA6CentreFor_POmegaMinus
    : OddLieA6CentreFor .POmegaMinus := by
  intro J _ n p f hp hp2 hadm hm α hα
  have hC : StatedClassicalModel J .POmegaMinus n p f :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) (EvenOrthSelector.statedModel_of_lieModel (by decide) hm) hn K hK b c
    hirr e
  refine a6CentreForm_of_semilinearRepresentation hrep
    (coordinateMinusWitnessEquiv K hn b c e) (fun g hσ2 hord => ?_) α hα
  by_cases hσ : g.val.right = 1
  · exact a6_omegaMinus_linear n hn K p f hp hp2 hK hadm b c hirr g hσ hord
  · exact a6_omegaMinus_field n hn K p f hp hp2 hK hadm b c hirr g hσ2 hσ hord

end CFSG.ComponentClassification.CatLeafProof
