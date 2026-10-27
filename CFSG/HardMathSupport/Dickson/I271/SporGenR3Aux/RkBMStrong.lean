module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22Shape
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Pair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThreeClose

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

section Fi22

theorem sporStrong_Fi22_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hChev : ChevStrong 3) : SporStrong .Fi22 3 :=
  sporStrong_of_leafShape_cover hOut hBr sporadicOnePairHolds_Fi22_three hChev leafShape_Fi22

end Fi22

section Fi24

theorem sporStrong_Fi24Prime_three_of_leafShape (hOut : SporadicOuterLeTwo)
    (hBr : SporadicBridges) (hChev : ChevStrong 3) (hD : LeafShape .Fi24Prime 3) :
    SporStrong .Fi24Prime 3 :=
  sporStrong_of_leafShape_cover hOut hBr sporadicOnePairHolds_Fi24_three hChev hD

end Fi24

section Th

theorem sporStrong_Th_three_of_leafShape (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hChev : ChevStrong 3) (hD : LeafShape .Th 3) : SporStrong .Th 3 :=
  sporStrong_of_leafShape_cover hOut hBr sporadicOnePairHolds_Th_three hChev hD

end Th

end CFSG.HardMathSupport.Dickson.I271
