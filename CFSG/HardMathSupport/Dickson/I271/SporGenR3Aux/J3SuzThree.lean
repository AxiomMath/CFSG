module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.CoverA6

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census


theorem sporStrong_J3_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .J3 3) (hChev : ChevStrong 3)
    (hD : CentShapeSplit 3 (NativeSporadic.Carrier .J3)) : SporStrong .J3 3 :=
  sporStrong_of_centShapeSplit_cover hOut hBr hP hChev hD

theorem sporPair_J3_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .J3 3) (hChev : ChevStrong 3)
    (hD : CentShapeSplit 3 (NativeSporadic.Carrier .J3)) : SporPair .J3 3 :=
  sporPair_of_sporStrong (sporStrong_J3_three hOut hBr hP hChev hD)

theorem sporStrong_Suz_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Suz 3) (hChev : ChevStrong 3)
    (hD : CentShapeSplit 3 (NativeSporadic.Carrier .Suz)) : SporStrong .Suz 3 :=
  sporStrong_of_centShapeSplit_cover hOut hBr hP hChev hD

theorem sporPair_Suz_three (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Suz 3) (hChev : ChevStrong 3)
    (hD : CentShapeSplit 3 (NativeSporadic.Carrier .Suz)) : SporPair .Suz 3 :=
  sporPair_of_sporStrong (sporStrong_Suz_three hOut hBr hP hChev hD)

end CFSG.HardMathSupport.Dickson.I271
