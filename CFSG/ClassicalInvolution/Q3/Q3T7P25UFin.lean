module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25U04
public import CFSG.ClassicalInvolution.Q3.Q3T7P25VFin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMFin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25



theorem parityE4Three_of_om6ReflDiag (hnc4 : NC4Three)
    (h2 : Q3T8.Asc77.CX.Om6ReflDiag) : ParityE4Three := by
  have : Q3T8.Asc77.CX.Facts25V :=
    ⟨by intros; exact hnc4, by intros; exact layer5SqThree_proved, layerTwinFactsFive3_proved⟩
  exact Q3T8.Asc77.CX.parityE4_of_om6ReflDiag h2

end CFSG.ClassicalInvolution.Q3.Q3T7P25
