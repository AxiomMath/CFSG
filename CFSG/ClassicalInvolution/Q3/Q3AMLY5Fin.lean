module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Top
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Sect
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Z
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5T
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5L

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

section Assembly


theorem cfby_of_axis_vertexA (hAxis : E4AxisLeafY) (hVA : VertexALeafY) : CFBY :=
  cfby_of_leaves ⟨hAxis, e2Y_proved, Q3T8.Asc77.e3zY_proved, Q3T8.Asc77.e3tY_proved, hVA,
    Q3T8.Asc77.e4linkY_proved⟩

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3AM
