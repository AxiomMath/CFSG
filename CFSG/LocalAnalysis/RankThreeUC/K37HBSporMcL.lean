module

public import CFSG.LocalAnalysis.RankThreeUC.K37HBSpor
public import CFSG.HardMathSupport.Dickson.I271.SporGenRank3
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.Coordinator

section Holds

set_option linter.unusedSectionVars false


theorem k37Rest₁₂_holds : K37Rest₁₂ := by
  intro X _ _ K E S h hO
  obtain ⟨-, h3z, hK⟩ := hO
  have h3 : 3 ∣ Nat.card K := h3z.trans (Subgroup.card_subgroup_dvd_card _)
  exact k37b_rest_of_sporStrong
    (sporStrong_McL_three CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group) h h3 hK

end Holds

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end
