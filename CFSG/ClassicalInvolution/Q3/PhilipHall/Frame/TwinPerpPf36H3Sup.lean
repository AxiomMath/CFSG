module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf27Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWSup23
public import CFSG.ClassicalInvolution.Q3.Sec13EndFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf36H3Leaves

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace CFSG.ClassicalInvolution.Q8P.P24

theorem sup23_2P_proved : Sup23_2P :=
  sup23_2P_of_thmEQ8W
    (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.thmEQ8_of_dLeafEnd
      (CFSG.ClassicalInvolution.Q3.Sec13.dLeafEnd_three _))

end CFSG.ClassicalInvolution.Q8P.P24

namespace CFSG.ClassicalInvolution.Q8P.Asc77.S24B

theorem h3_of_leaves (hA : CentralizeH) (hB : TransCentral) : H3 :=
  haveI : Fact P24.Sup23_2P := ⟨P24.sup23_2P_proved⟩
  h3_of_transCentral hA hB

end CFSG.ClassicalInvolution.Q8P.Asc77.S24B
