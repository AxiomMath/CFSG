module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryPieces
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaInputs

public section

namespace CFSG.SeitzReduction.F4Pilot

section Final

theorem graphPieceTablesInput_of_omega (hO : OmegaPieceTablesInput) : GraphPieceTablesInput :=
  graphPieceTablesInput_of_pieces_omega unitaryModelPiecesInput_holds hO

theorem graphPieceTablesInput_of_models (hP : GraphKindModelInput .omegaPlus8)
    (hM : GraphKindModelInput .omegaMinus8) : GraphPieceTablesInput :=
  graphPieceTablesInput_of_omega (omegaPieceTablesInput_of_models hP hM)

end Final

end CFSG.SeitzReduction.F4Pilot
