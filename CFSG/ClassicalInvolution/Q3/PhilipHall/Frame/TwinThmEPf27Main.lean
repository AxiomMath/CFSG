module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf20Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf21E4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf22AE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf24Red
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf23Orb4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf26U3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHullPf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuotCentPf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf18OddCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf15Supply
public import CFSG.ClassicalInvolution.Q3.TL3T12_6E29Main
public import CFSG.ClassicalInvolution.Q3.Sec13E4
public import CFSG.ClassicalInvolution.Q3.Sec13Star
public import CFSG.ClassicalInvolution.Q3.TL3T77

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3

namespace TwinThmEW

section Main



theorem thmEQ8_of_open (hD : D2Supply) : ThmEQ8 := by
  haveI : PrintedQuotOdd := printedQuotOdd_proved
  haveI : PrintedHull := printedHull_proved
  haveI : PrintedQuotCent := printedQuotCent_proved
  exact thmEQ8_of_inputs15 t4Supply_of_twoClass hD
    { orbit4 := e187Orbit4Q8_proved,
      reduce := e189ReduceQ8'_of_model t4Supply_of_twoClass TwinDisc.ExitE4.e4ModelDStar_of_certs,
      ae5Branch := e189AE5Q8_proved, e4 := TwinThmE.e189E4ModelT_of_certs,
      u3 := e178U3Q8_of_twin }

open CFSG.ClassicalInvolution.Q3.TC.Thin in
theorem thmEQ8_of_open'
    (hAE : CLeafAE 3 (PackIH 3)) (hEnd : DLeafEnd 3 (PackIH 3)) :
    ThmEQ8 :=
  thmEQ8_of_open (d2Supply_of_leaves (cLeaf126_proved (PackIH 3)).1 (cLeaf126_proved (PackIH 3)).2.1
    (cLeaf126_proved (PackIH 3)).2.2 hAE (Sec13.dLeafE4_three (PackIH 3))
    (Sec13.dLeafStar_three (PackIH 3)) hEnd)

open CFSG.ClassicalInvolution.Q3.TC.Thin in
theorem thmEQ8_of_dLeafEnd
    (hEnd : DLeafEnd 3 (PackIH 3)) : ThmEQ8 :=
  thmEQ8_of_open' (cLeafAE_holds (PackIH 3)) hEnd

end Main

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
