module

public import CFSG.ClassicalInvolution.Q3.Q3DInputs7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight

theorem ih8T_of_cit3Below {n : ℕ} (h : CIT3Below n) : IH8T 3 1 n :=
  Disc3.ih8T_three_proved n ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr h)

end CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge
