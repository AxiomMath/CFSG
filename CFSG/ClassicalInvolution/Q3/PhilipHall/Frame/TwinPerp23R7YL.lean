module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7N2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E64CenComm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Steps

variable {n : ℕ}

theorem p23E7Y_of_lemL_e64 (hT : Thm4RTwinBelow 3 n) (hT4 : TwinThmE.T4Supply)
    (hmodel : TwinDisc.ExitE4.E4ModelDStar) (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n)
    (hTwo : P23Two n) (hα : P23Alpha n) (hL : P23E7LemL n) : P23E7Y n :=
  p23E7Y_of_lemL' hT hT4 hmodel hD4 hMu hTwo hα hL E64CC.e64CenComm_proved

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
