module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22BDW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ELayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section LayerW

variable {n : ℕ}

theorem v3LayerDW_of_thmE (hE : TwinThmE.TwinThmEP n)
    (hcit : CIT3Below n) (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n)
    (hSp : TwinCentRes.ModelFactSp62) (hD4 : TwinCentRes.ModelFactD42) (h4 : Thm4RTwinBelow 3 n)
    (hB : V3Hyp51B n) (h5 : V3Fourth n) (h7 : V3Alpha13 n) : V3LayerDW n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ hStd h2g W hW hKW hu₁ hu₂ hV J hJ hJc
  have hO := oddCent_eq_bot_of_thmE hE hcit hP hSp hD4 h4 hB h5 h7 hStd
  have hOxy := oddCent_prod_eq_bot hSp hD4 h4 hcit hP hB h5 h7 hStd hO
  exact v3LayerDWO_proved n Y R S t K K' K₃ u₁ u₂ u₃ hStd h2g hOxy W hW hKW hu₁ hu₂ hV J hJ hJc

end LayerW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
