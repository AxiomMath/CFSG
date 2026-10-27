module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf12Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2E8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Pf14E8

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

theorem e8ExitQ8_proved : E8ExitQ8 :=
  fun _ _ _ _ F ⟨_, hE⟩ => TwinDisc.ExitO2.fam_dstarConnected_of_e8 F hE

end Pf14E8

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
