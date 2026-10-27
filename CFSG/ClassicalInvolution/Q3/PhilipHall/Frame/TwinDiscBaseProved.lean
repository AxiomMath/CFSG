module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPfExc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Wire

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc


theorem twinDiscBase_of_thm4 {n : ℕ} (h4 : Thm4RTwinBelow 3 n) : TwinDiscBase n :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ s => alphaStepsBaseV₃ TwinExitPf10.twinDiscBaseV₃_proved h4 s

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
