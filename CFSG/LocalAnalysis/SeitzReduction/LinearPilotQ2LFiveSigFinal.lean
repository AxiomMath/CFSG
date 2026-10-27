module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSigMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeSplitModule

public section

namespace CFSG.SeitzReduction.LinearPilot

theorem lFiveGraphLeviNormInput_holds :
    LFiveGraphLeviNormInput :=
  lFiveGraphLeviNormInput_of_fieldModule lFiveWOneFieldModuleInput_holds

end CFSG.SeitzReduction.LinearPilot
