module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrLE8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Step


theorem frameCaseIITGN_proved :
    Frame.FrameAEmptyPf.FrameCaseIITGN :=
  Frame.FrameAEmptyPf.frameCaseIITGN_of_nbrTwinG
    (Frame.FrameAEmptyPf.frameNbrTwinSG_of_hyp51L Frame.FrameAEmptyPf.frameHyp51L_holds)

theorem thm3RStdSimple_proved
    (m : ℕ) : Thm3RStdSimple m :=
  thm3RStdSimple_of_caseII frameCaseIITGN_proved m

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
