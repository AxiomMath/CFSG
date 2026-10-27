module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch

public section

namespace CFSG.AGLEmbedding

theorem kFactCompParabSU38_of_families (hA : KFactCompParabSU38On (IsLieOf IdxA))
    (h2A : KFactCompParabSU38On (IsLieOf IdxTwistedA)) (hB : KFactCompParabSU38On (IsLieOf IdxB))
    (hD : KFactCompParabSU38On (IsLieOf IdxD)) (h2D : KFactCompParabSU38On (IsLieOf IdxTwistedD))
    (hG : KFactCompParabSU38On (IsLieOf IdxG2)) (hS : KFactCompParabSU38On IsSmallTwoOrG2) :
    KFactCompParabSU38 := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

theorem kFactCompParabLeviU42_of_families (hA : KFactCompParabLeviU42On (IsLieOf IdxA))
    (h2A : KFactCompParabLeviU42On (IsLieOf IdxTwistedA))
    (hB : KFactCompParabLeviU42On (IsLieOf IdxB)) (hD : KFactCompParabLeviU42On (IsLieOf IdxD))
    (h2D : KFactCompParabLeviU42On (IsLieOf IdxTwistedD))
    (hG : KFactCompParabLeviU42On (IsLieOf IdxG2)) (hS : KFactCompParabLeviU42On IsSmallTwoOrG2) :
    KFactCompParabLeviU42 := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

theorem kFactCompParabThreeFives_of_families (hA : KFactCompParabThreeFivesOn (IsLieOf IdxA))
    (h2A : KFactCompParabThreeFivesOn (IsLieOf IdxTwistedA))
    (hB : KFactCompParabThreeFivesOn (IsLieOf IdxB))
    (hD : KFactCompParabThreeFivesOn (IsLieOf IdxD))
    (h2D : KFactCompParabThreeFivesOn (IsLieOf IdxTwistedD))
    (hG : KFactCompParabThreeFivesOn (IsLieOf IdxG2))
    (hS : KFactCompParabThreeFivesOn IsSmallTwoOrG2) : KFactCompParabThreeFives := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

end CFSG.AGLEmbedding
