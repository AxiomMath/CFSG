module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4SocleFacts
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Assembly

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.HardMathSupport.Malle.OvergroupTransport

theorem reeF4SocleFiveRank_of_certs :
    ReeF4SocleFiveRank := by
  intro K _ _ d hd e P hP
  exact pRank_le_two_of_isPGroup hd e P hP

theorem reeF4SocleAutOrder_of_certs :
    ReeF4SocleAutOrder := by
  intro K _ _ d hd e
  exact card_mulAut_dvd_five_mul hd e

end CFSG.HardMathSupport.Malle.LocalAction
