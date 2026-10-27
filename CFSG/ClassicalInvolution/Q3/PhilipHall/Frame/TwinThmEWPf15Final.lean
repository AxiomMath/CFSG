module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf9Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinCore
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution

namespace TwinThmE

theorem t4Supply_proved : T4Supply :=
  thm4RTwin_of_twoClass fun _ hA hP => TL4.exitTwoClassR_of hA hP

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
