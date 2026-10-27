module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexSaturation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernels

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex

open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.HighRankPair

theorem unitaryMonomialTheorem_of_kernels
    (G : Type) [Group G] [Finite G]
    (hker : UnitaryInvolutoryKernelsConclusion G) : UnitaryMonomialTheorem G :=
  unitaryMonomialTheorem_of_pairGeneration G (fun H z h _ hbeta _ ht => by
    rw [← minimalLocalFailureProperPairHull_eq_native]
    exact PairGeneration.pair_generated_hull_eq_top G H z h hbeta ht) hker

theorem unitaryMonomialTheorem
    (G : Type) [Group G] [Finite G] : UnitaryMonomialTheorem G :=
  unitaryMonomialTheorem_of_kernels G (UnitaryKernels.unitaryInvolutoryKernelsConclusion G)

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex
