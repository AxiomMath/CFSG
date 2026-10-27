module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203ZTwo

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf


theorem frame203TwoPart_holds : Frame203TwoPart := by
  intro G _ _ _ K K' J S R R' W V z t d
  exact padicValNat_index_N203_le_one d

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
