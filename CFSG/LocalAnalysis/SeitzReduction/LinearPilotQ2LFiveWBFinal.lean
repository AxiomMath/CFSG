module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWB
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBRad

public section

namespace CFSG.SeitzReduction.LinearPilot

theorem lFiveRadicalInput : LFiveRadicalInput := fun _ _ _ _ hK _ hz _ hRz hRn hRc =>
  exists_mulAut_map_eq_pointRadical hK hz hRz hRn hRc

theorem lFiveWOneInput : LFiveWOneInput :=
  lFiveWOneInput_of_radical lFiveRadicalInput

end CFSG.SeitzReduction.LinearPilot
