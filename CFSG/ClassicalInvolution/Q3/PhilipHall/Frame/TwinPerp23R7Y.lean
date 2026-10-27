module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Orb

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section E7Y

variable {n : ℕ}

theorem p23E7Y_of_orb (hT : Thm4RTwinBelow 3 n)
    (hT4 : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) (hOrb : P23E7Orb n)
    (hO : GoldOutCyc) : P23E7Y n :=
  p23E7Y_of_fus' hT hT4 hmodel hD4 hMu hOrb p23E7Fus_proved hO

theorem p23E7Y_of_e8 (hT : Thm4RTwinBelow 3 n)
    (hT4 : TwinThmE.T4Supply) (hmodel : TwinDisc.ExitE4.E4ModelDStar)
    (hD4 : TwinCentRes.ModelFactD42) (hMu : P23E4Mu n) (hE8 : P23E7E8 n)
    (hO : GoldOutCyc) : P23E7Y n :=
  p23E7Y_of_orb hT hT4 hmodel hD4 hMu (p23E7Orb_of_e8 hE8) hO

end E7Y

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
