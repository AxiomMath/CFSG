module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeakSimple

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.Monster.Generated (Gmat)

@[expose] def MSevenShapeGmat : Prop :=
  CentShapeRk' 7 (GoodSpor 7 [.He]) (RkSpor 7 [.He]) Gmat

section Pair


theorem sporPair_M_seven_of_gmatShape
    (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M 7) (hChev : ChevStrong 7)
    (hHe : SporStrong .He 7) (hD : MSevenShapeGmat) : SporPair .M 7 :=
  sporPair_M_of_gmatShape (by norm_num) hOut hSpM hBr hP hChev
    (fun S hS => by
      simp only [List.mem_singleton] at hS
      subst hS
      exact hHe) hD

end Pair

end CFSG.HardMathSupport.Dickson.I271
