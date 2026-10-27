module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203TwoPart
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203CentOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf


theorem frame203Cent_holds : Frame203Cent :=
  frame203Cent_of_twoPart frame203TwoPart_holds frameCentOdd_holds

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
