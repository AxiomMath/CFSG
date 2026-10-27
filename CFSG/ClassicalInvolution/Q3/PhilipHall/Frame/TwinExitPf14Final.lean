module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf14Step

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance

namespace TwinDisc

theorem nonExactTwin_of_nonTight_proved {n : ℕ} (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h : NonTightTwin n) : NonExactTwin n :=
  nonExactTwin_of_nonTight TwinCentRes.modelFactSp62 TwinCentRes.modelFactD42_of_cert hcit hP h

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
