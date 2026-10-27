module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerOLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmega
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.Assembly.GL83LieDefs

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem oddOmegaOddLinearInput_of_orthogonalComponents
    (hO : ∀ p : ℕ, p.Prime → p ≠ 2 → OddInner.OrthogonalComponentsLie p) :
    OddOmegaOddLinearInput := by
  intro n K _ _ p f hp hp2 hK hadm g hg hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_odd hstated K hK (MulEquiv.refl _)
  exact oddLie_inner_omega (hO p hp hp2) hp hp2 hadm.2.1 hK (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord hL

theorem oddOmegaPlusLinearInput_of_orthogonalComponents
    (hO : ∀ p : ℕ, p.Prime → p ≠ 2 → OddInner.OrthogonalComponentsLie p) :
    OddOmegaPlusLinearInput := by
  intro n K _ _ p f hp hp2 hK hadm g hg hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus
      n p f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus hstated K hK (MulEquiv.refl _)
  have hn : 4 ≤ n := hadm.2.2
  exact oddLie_inner_omega (hO p hp hp2) hp hp2 hadm.2.1 hK (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord hL

theorem oddOmegaMinusLinearInput_of_orthogonalComponents
    (hO : ∀ p : ℕ, p.Prime → p ≠ 2 → OddInner.OrthogonalComponentsLie p) :
    OddOmegaMinusLinearInput := by
  intro n hn K _ _ p f hp hp2 hK hadm b c hirr g hg hord L hL
  have hstated : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K b c)))
      .POmegaMinus n p f := ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr,
        ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, hnd, hT, -, hAP, -⟩ :=
    coordinate_model_witness_minus hstated K hK b c hirr (MulEquiv.refl _)
  exact oddLie_inner_omega (hO p hp hp2) hp hp2 hadm.2.1 hK (by omega) hnd
    (RankThree.Classical.SteinbergBY.matrixProjectiveConjugationHom_eq_one_iff _ hnd hT hAP) g
    hg hord hL

end CFSG.ComponentClassification.CatLeafProof
