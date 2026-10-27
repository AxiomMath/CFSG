module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X14
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T7
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25AE5Sq

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.ClassicalInvolution.Q8P.Asc77.P25R CFSG.ClassicalInvolution.Q8P.Asc77.P25T
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


theorem typedL_proved : P25_TypedL :=
  p25_typedL_of_exits TwinThmE.t4Supply_proved TwinDisc.oddCentEdge_proved p25_typedO2_proved
    p25_typedE4_proved

theorem sqZL_proved : P25X_SqZL :=
  sqZLAt_of_layerSq TwinThmE.t4Supply_proved
    (p25_sqLayer_of_typedL ae5SqModel_of_cert typedL_proved)

theorem p25_a4_of_noFace (hNF : P25X_NoFace) : P25_A4 :=
  a4_of_leaves (qtf_of_typedL typedL_proved) sqZL_proved hNF

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
