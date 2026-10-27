module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoONOuter
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2SporadicAssembly

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Assembly

theorem starPrime_of_gls3_of_oddLie (hGLS : GLS3OddLieAutComponentsInput)
    (hO : CatSL2OddLieBound 2) {f : ℕ} (hf : 2 ≤ f) : StarPrimeStatement f :=
  starPrime_of_gls3_of_two_le hGLS hO onOuterSL2Input_holds hf

end Assembly

end CFSG.SeitzReduction.RankOne
