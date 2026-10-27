module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def L2UnbalancingOuterFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J →
    (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J)) →
    ∀ j ∈ J, j⁻¹ * x ∉ coreActionKernel J

end CFSG.ComponentClassification.GrSLit
