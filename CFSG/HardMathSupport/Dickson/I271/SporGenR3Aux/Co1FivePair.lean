module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeMulti

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4

section Co1

theorem sporStrong_Co1_five
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Co1 5) (hChev : ChevStrong 5) (hJ2 : SporStrong .J2 5)
    (hD : CentShapeMulti 5 (GoodSpor 5 [.J2]) (RkSpor 5 [.J2]) (NativeSporadic.Carrier .Co1)) :
    SporStrong .Co1 5 :=
  sporStrong_of_goodSporMultiShape hOut hSpM hBr hP (by decide) hChev
    (fun S hS => by
      simp only [List.mem_singleton] at hS
      subst hS
      exact hJ2) hD

theorem sporPair_Co1_five
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .Co1 5) (hChev : ChevStrong 5) (hJ2 : SporStrong .J2 5)
    (hD : CentShapeMulti 5 (GoodSpor 5 [.J2]) (RkSpor 5 [.J2]) (NativeSporadic.Carrier .Co1)) :
    SporPair .Co1 5 :=
  sporPair_of_sporStrong (sporStrong_Co1_five hOut hSpM hBr hP hChev hJ2 hD)

end Co1

end CFSG.HardMathSupport.Dickson.I271
