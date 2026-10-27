module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaPieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowMinusOut

public section

namespace CFSG.SeitzReduction.SymplecticPilot


theorem spOmegaPlusRowInput_of_unique (hu : SpOmegaRowUniqueInput .omegaPlus) :
    SpOmegaPlusRowInput :=
  false_of_spOmegaPlusRow_of_kind spOmegaKindInput_omegaPlus_holds hu

theorem spOmegaMinusRowInput_of_pieces_of_unique (hp : SpOmegaMinusPieceInput)
    (hu : SpOmegaRowUniqueInput .omegaMinus) : SpOmegaMinusRowInput :=
  false_of_spOmegaMinusRow_of_kind' (spOmegaKindInput_omegaMinus_of_pieceInput hp) hu

end CFSG.SeitzReduction.SymplecticPilot
