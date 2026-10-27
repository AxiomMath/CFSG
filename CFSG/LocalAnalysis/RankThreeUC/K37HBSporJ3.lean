module

public import CFSG.LocalAnalysis.RankThreeUC.K37HBSpor
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ChevStrongD4
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.J3SuzThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabJ3Shape
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Assemble
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census

section Holds

set_option linter.unusedSectionVars false


theorem k37Rest₁₁_holds : K37Rest₁₁ := by
  intro X _ _ K E S h hO
  obtain ⟨-, h3z, hK⟩ := hO
  have h3 : 3 ∣ Nat.card K := h3z.trans (Subgroup.card_subgroup_dvd_card _)
  have hBr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  exact k37b_rest_of_sporStrong
    (sporStrong_J3_three CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds hBr
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOnePairHolds_J3 (hBr .J3))
      (chevStrong_holds 3) centShapeSplit_J3) h h3 hK

end Holds

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
