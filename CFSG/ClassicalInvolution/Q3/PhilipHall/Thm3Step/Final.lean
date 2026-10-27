module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwinFactsQ8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A


theorem thm3RStepGAll_proved :
    ∀ m, Thm3RStepG m :=
  thm3RStepG_of_remaining S7Ident.twinQ8Class_proved

theorem frameAEmptyP_proved :
    Frame.FrameAEmptyPf.FrameAEmptyP :=
  Frame.FrameAEmptyPf.frameAEmptyP_of_casesTG thm3RStepGAll_proved
    Frame.FrameAEmptyPf.frameCaseITG_proved Frame.FrameAEmptyPf.frameCaseIITG_proved

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
