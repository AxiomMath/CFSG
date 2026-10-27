module

public import CFSG.LocalAnalysis.ComponentClassification.GS82P7
public import CFSG.LocalAnalysis.ComponentClassification.GS82P8
public import CFSG.LocalAnalysis.ComponentClassification.GS82PC

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

theorem sLTwoCentralPumpInput_holds
    : SLTwoCentralPumpInput :=
  sLTwoCentralPumpInput_of_typPump typPumpInput_holds

theorem spFourThreeCentralPumpInput_holds
    : SpFourThreeCentralPumpInput :=
  spFourThreeCentralPumpInput_of_typPump typPumpInput_holds

end CFSG.ComponentClassification.GS82PumpInputs
