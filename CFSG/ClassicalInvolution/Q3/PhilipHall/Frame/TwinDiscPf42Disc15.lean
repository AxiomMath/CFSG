module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf41ZT
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetWire
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf27Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Pairs

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Wire


theorem twinDiscPerpSPAll_of_disc15
    (hLEnd : CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafEnd 3
      (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3))
    (h15 : ∀ n, CIT3Below n → CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n →
      TwinDisc.Disc15 n) :
    ∀ n, TwinCoreDiscPerpSP n := by
  haveI : TwinThmEW.PrintedQuotOdd := TwinThmEW.printedQuotOdd_proved
  haveI : TwinThmEW.PrintedQuotCent := TwinThmEW.printedQuotCent_proved
  haveI : TwinThmEW.PrintedHull := TwinThmEW.printedHull_proved
  have hWF : TwinThmEW.WFreeToAll := TwinThmEW.wFreeToAll_proved
  have hEQ : TwinThmEW.ThmEQ8 := TwinThmEW.thmEQ8_of_dLeafEnd hLEnd
  intro n hA hP Y _ _ R S t h hD hPerp
  exact TwinDisc.twinCoreDiscPerp_of_inputsPf36
    (TwinThmEW.twinThmE_of_thmEQ8W hEQ hWF hA hP) (h15 n hA hP)
    (TwinThmEW.t4Supply_of_twoClass n hA hP) hA hP Y R S t h.toHyp hD hPerp



theorem twinDiscPerpSPAll_of_disc15T
    (hLEnd : CFSG.ClassicalInvolution.Q3.TC.Thin.DLeafEnd 3
      (CFSG.ClassicalInvolution.Q3.TC.Thin.PackIH 3))
    (h15 : ∀ n, CIT3Below n → CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n →
      TwinDisc.Disc15T n) :
    ∀ n, TwinCoreDiscPerpSP n :=
  twinDiscPerpSPAll_of_disc15 hLEnd fun n hA hP =>
    TwinDisc.disc15_of_disc15T (TwinDisc.twinDiscBase_of_thm4 (TwinThmEW.t4Supply_of_twoClass n hA hP))
      (h15 n hA hP)

end Wire

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
