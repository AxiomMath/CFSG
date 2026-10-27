module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoCent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoSU

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem lFiveGraphCosetThreeInput_of_xInput (hX : LFiveGraphXInput) :
    LFiveGraphCosetThreeInput :=
  lFiveGraphCosetThreeInput_of_X hX sLThreeGraphFieldFixInput

theorem lFiveGraphCosetThreeInput_of_xCentralInput (hX : LFiveGraphXCentralInput) :
    LFiveGraphCosetThreeInput :=
  lFiveGraphCosetThreeInput_of_XCentral hX sLThreeGraphFieldFixInput

end CFSG.SeitzReduction.LinearPilot
