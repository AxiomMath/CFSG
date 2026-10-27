module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24HFin
public import CFSG.ClassicalInvolution.Q3.Q3T7P24V01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.ClassicalInvolution.Q3.Q3T7


theorem c24_1Three_of_thmE' (hE : Q3T7E.ThmEWithSylow3) (h51 : Hyp51TwinInnerThree) :
    C24_1Three :=
  c24_1Three_of_thmE hE ⟨hyp51VertexThree_proved, h51⟩

end CFSG.ClassicalInvolution.Q3.Q3T7P24
