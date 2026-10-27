module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthAll

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.ComponentClassification.CatLeaf

theorem oddInner_orthogonalComponentsLie (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    OddInner.OrthogonalComponentsLie p :=
  orthogonalComponentsLie_holds hp hp2

theorem oddOmegaOddLinearInput_holds : OddOmegaOddLinearInput :=
  oddOmegaOddLinearInput_of_orthogonalComponents oddInner_orthogonalComponentsLie

theorem oddOmegaPlusLinearInput_holds : OddOmegaPlusLinearInput :=
  oddOmegaPlusLinearInput_of_orthogonalComponents oddInner_orthogonalComponentsLie

theorem oddOmegaMinusLinearInput_holds : OddOmegaMinusLinearInput :=
  oddOmegaMinusLinearInput_of_orthogonalComponents oddInner_orthogonalComponentsLie

end CFSG.ComponentClassification.CatLeafProof
