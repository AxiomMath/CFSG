module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203BFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf


theorem frameCentOdd_holds : FrameCentOdd := by
  intro G _ _ _ K K' J S R R' W V z t d hpad x hxX hxK hxK'
  exact cent203b_main d hpad hxX hxK hxK'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
