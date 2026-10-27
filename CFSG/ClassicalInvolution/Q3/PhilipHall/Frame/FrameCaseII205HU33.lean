module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFBase
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3


theorem frameU33_autOddFree (hU : TL4.OuterFixedOddFree .PSU 3) {N : Type} [Group N] [Finite N]
    [IsSimpleGroup N] (hN : CFSG.Blueprint.LieModel N .PSU 3 3 1) : Q3NM.AutOddFree N :=
  TL4.autOddFree_of_outer (t := .PSU) (n := 3) (by simp) (by simp) (by trivial) (by trivial)
    hN (hU N (by assumption) hN)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
