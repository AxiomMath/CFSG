module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables

public section

namespace CFSG.SeitzReduction.F4Pilot

@[expose] def twoDiagPieceOrder : Sp6Kind → ℕ
  | .field => 979200
  | .swap => 129600
  | .linear6 => 20160
  | .unitary6 => 25920
  | .linear7 => 9999360
  | .unitary7 => 13685760
  | .omegaPlus8 => 25920
  | .omegaMinus8 => 20160

end CFSG.SeitzReduction.F4Pilot
