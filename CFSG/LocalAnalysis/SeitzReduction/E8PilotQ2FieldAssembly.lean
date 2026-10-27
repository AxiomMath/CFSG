module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2FieldMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

theorem e8TwoFieldRowInput_of_pieceInput (hP : E8TwoFieldPieceInput) : E8TwoFieldRowInput := by
  intro G _ _ L K _ e t hw hF
  obtain ⟨A, hAJ, hA, htX, hFk⟩ := hF
  exact false_of_fieldRow_E8_two_of_pieceInput hP hw e hAJ hA htX hFk

end CFSG.SeitzReduction.E8Pilot
