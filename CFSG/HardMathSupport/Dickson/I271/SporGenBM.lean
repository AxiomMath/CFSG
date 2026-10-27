module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census

section Shapes

@[expose] def BThreeShape : Prop :=
  CentShapeRk' 3 (GoodSpor 3 [.Fi22]) (RkSpor 3 [.Fi22]) (NativeSporadic.Carrier .B)

@[expose] def MThreeShape : Prop :=
  CentShapeRk' 3 (GoodSpor 3 [.Fi24Prime, .Th]) (RkSpor 3 [.Fi24Prime, .Th])
    (NativeSporadic.Carrier .M)

@[expose] def BFiveShape : Prop :=
  CentShapeRk' 5 (GoodSpor 5 [.HS]) (RkSpor 5 [.HS]) (NativeSporadic.Carrier .B)

@[expose] def MFiveShape : Prop :=
  CentShapeRk' 5 (GoodSpor 5 [.HN]) (RkSpor 5 [.HN]) (NativeSporadic.Carrier .M)

end Shapes

section Pairs

theorem sporPair_B_three_of_shape
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .B 3) (hChev : ChevStrong 3)
    (hFi22 : SporStrong .Fi22 3) (hD : BThreeShape) : SporPair .B 3 :=
  sporPair_of_sporStrong
    (sporStrong_of_goodSporShape' hOut hSpM hBr hP (by decide) hChev
      (fun S hS => by
        simp only [List.mem_singleton] at hS
        subst hS
        exact hFi22) hD)

theorem sporPair_M_three_of_shape
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 3) (hChev : ChevStrong 3)
    (hFi24 : SporStrong .Fi24Prime 3) (hTh : SporStrong .Th 3) (hD : MThreeShape) :
    SporPair .M 3 :=
  sporPair_of_sporStrong
    (sporStrong_of_goodSporShape' hOut hSpM hBr hP (by decide) hChev
      (fun S hS => by
        rcases List.mem_cons.1 hS with rfl | hS
        · exact hFi24
        · obtain rfl := List.mem_singleton.1 hS
          exact hTh) hD)

theorem sporPair_B_five_of_shape
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .B 5) (hChev : ChevStrong 5)
    (hHS : SporStrong .HS 5) (hD : BFiveShape) : SporPair .B 5 :=
  sporPair_of_sporStrong
    (sporStrong_of_goodSporShape' hOut hSpM hBr hP (by decide) hChev
      (fun S hS => by
        simp only [List.mem_singleton] at hS
        subst hS
        exact hHS) hD)

theorem sporPair_M_five_of_shape
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 5) (hChev : ChevStrong 5)
    (hHN : SporStrong .HN 5) (hD : MFiveShape) : SporPair .M 5 :=
  sporPair_of_sporStrong
    (sporStrong_of_goodSporShape' hOut hSpM hBr hP (by decide) hChev
      (fun S hS => by
        simp only [List.mem_singleton] at hS
        subst hS
        exact hHN) hD)

end Pairs

end CFSG.HardMathSupport.Dickson.I271
