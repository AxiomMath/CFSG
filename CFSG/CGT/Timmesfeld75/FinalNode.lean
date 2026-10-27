module

public import CFSG.CGT.Timmesfeld75.FinalFlat

public section

namespace CFSG.CGT.Timmesfeld75

theorem theoremA_final (I : NodeInputs) : TheoremAStmt :=
  theoremA_of_flat multPrimeInput altCoverInput I

theorem node_final (I : NodeInputs) : NodeStatement :=
  node_of_flat multPrimeInput altCoverInput I

end CFSG.CGT.Timmesfeld75
