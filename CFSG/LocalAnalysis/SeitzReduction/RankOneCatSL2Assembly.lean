module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuterBound
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Alt
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Odd

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification

section Assembly


theorem catSL2Bound_of_oddLie_sporadic {n : ℕ} (hO : CatSL2OddLieBound n)
    (hS : CatSL2SporadicBound n) : CatSL2Bound n :=
  catSL2Bound_of_clauses (catSL2AlternatingBound n) (catSL2EvenOuterBound n) hO hS

theorem starPrime_of_oddLie_sporadic {f : ℕ} (hf : 2 ≤ f) (hO : CatSL2OddLieBound f)
    (hS : CatSL2SporadicBound f) : StarPrimeStatement f :=
  starPrime_of_catSL2 hf (catSL2Bound_of_oddLie_sporadic hO hS)

theorem catSL2Bound_of_inputs (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) {n : ℕ}
    (hX : SL2NotOddLieInputAt n) (hS : CatSL2SporadicBound n) : CatSL2Bound n :=
  catSL2Bound_of_oddLie_sporadic (catSL2OddLieBound_of_inputs hGLS hX) hS

theorem starPrime_of_inputs (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) {f : ℕ} (hf : 2 ≤ f)
    (hX : SL2NotOddLieInputAt f) (hS : CatSL2SporadicBound f) : StarPrimeStatement f :=
  starPrime_of_catSL2 hf (catSL2Bound_of_inputs hGLS hX hS)

end Assembly

end CFSG.SeitzReduction.RankOne
