module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7W714D
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Steps


variable {n : ℕ}

theorem p23E7Not9C_of_lemL (hL : P23E7LemL n) : P23E7Not9C n :=
  p23E7Not9C_of_LL (p23E7LL1_of_lemL hL) (p23E7LL2_of_lemL hL) (p23E7LL3_of_lemL hL)

theorem p23E7Not9_of_lemL (hL : P23E7LemL n) : P23E7Not9 n :=
  p23E7Not9_of_C (p23E7Not9C_of_lemL hL)

theorem p23E7Y_of_lemL_cen3 (hT : Thm4RTwinBelow 3 n)
    (hT4 : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) (hTwo : P23Two n) (hα : P23Alpha n)
    (hL : P23E7LemL n) (hC3 : P23E7Cen3 n) : P23E7Y n :=
  p23E7Y_of_not9_cen3 hT hT4 hmodel hD4 hMu hTwo hα (p23E7Not9_of_lemL hL) hC3

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
