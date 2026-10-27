module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmSixPlus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValUnitary

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

theorem twoRowsCatInput_of_rows (hF : TwoFieldPairInput) (hS : TwoSwapPairInput)
    (hE : TwoE6PairInput) (hT : TwoTwistedE6PairInput) : TwoRowsCatInput :=
  twoRowsCatInput_of_omegaValues twoOmegaPlusModelValues_holds twoOmegaMinusModelValues_holds hF
    hS hE hT

end CFSG.SeitzReduction.F4Pilot
