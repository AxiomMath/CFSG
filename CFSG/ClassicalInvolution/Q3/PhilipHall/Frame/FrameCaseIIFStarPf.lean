module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIIFStar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII206Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

section Closed


theorem frame206ClosedF_holds : Frame206ClosedF :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ d c8 c3 _ hS => d.closed_of_concl203 c8 c3 hS

end Closed

section Assembly


theorem frameCaseIITF_proved : FrameCaseIITF :=
  frameCaseIITF_of_closed frame206ClosedF_holds

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
