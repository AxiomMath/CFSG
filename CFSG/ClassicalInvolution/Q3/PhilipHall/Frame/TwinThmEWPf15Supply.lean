module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf12Six
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinCore
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Fin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution

namespace TwinThmEW


theorem t4Supply_of_twoClass : T4Supply :=
  thm4RTwin_of_twoClass fun _ hA hP => TL4.exitTwoClassR_of hA hP

open CFSG.ClassicalInvolution.Q3.TC.Thin in
theorem d2Supply_of_leaves (hE8 : CLeafE8 3 (PackIH 3)) (hE64 : CLeafE64 3 (PackIH 3))
    (hE29 : CLeafE29 3 (PackIH 3)) (hAE : CLeafAE 3 (PackIH 3)) (hE4 : DLeafE4 3 (PackIH 3))
    (hstar : DLeafStar 3 (PackIH 3)) (hend : DLeafEnd 3 (PackIH 3)) : D2Supply :=
  fun n => thmD2Step_of_leaves₆ hE8 hE64 hE29 hAE hE4 hstar hend n

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
