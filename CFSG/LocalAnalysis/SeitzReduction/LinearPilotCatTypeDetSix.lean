module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem slmEvenTypeDetAt_six : SLmEvenTypeDetAt 6 :=
  fun _ _ _ _ _ _ h6 _ h => F4Pilot.lieModel_PSL_six_two_unique h6 h

end CFSG.SeitzReduction.LinearPilot
