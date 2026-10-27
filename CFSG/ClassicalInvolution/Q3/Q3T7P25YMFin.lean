module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25Fin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25VH00
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YM01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25



theorem layer5SqThree_proved : Layer5SqThree :=
  Q3T8.Asc77.C25W.layer5Sq_proved

theorem cent5Three_proved : Q3T8.Asc77.C25W.Cent5 :=
  Q3T8.Asc77.C25W.cent5_proved

theorem layerTwinFactsFive3_proved : Q3T8.Asc77.CX.LayerTwinFactsFive3 := by
  unfold Q3T8.Asc77.CX.LayerTwinFactsFive3
  intros
  exact Q3T8.Asc77.CX.layerTwinFacts_five_proved (by assumption) (by assumption) (by assumption)
    (by assumption)

end CFSG.ClassicalInvolution.Q3.Q3T7P25
