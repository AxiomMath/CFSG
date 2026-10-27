module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3E
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf15Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf15Odd

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap



theorem p25_sqZ_of_exits_proved (hAE : AE5SqModel) (h2 : P25_TypedO2) (h3 : P25_TypedE4) :
    P25S.P25_SqZ :=
  p25_sqZ_of_exits TwinThmE.t4Supply_proved TwinDisc.oddCentEdge_proved hAE h2 h3

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
