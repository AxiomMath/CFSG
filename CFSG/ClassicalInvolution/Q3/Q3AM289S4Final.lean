module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4Main
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4MSU01
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4MOdd
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4MMin
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LAll

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

section Final


theorem s4VertexModelLeaf_proved : S4VertexModelLeaf :=
  ⟨s4VertexModelLeafAt_psu4, s4VertexModelLeafAt_odd3, s4VertexModelLeafAt_minus4⟩

theorem pspS4Leaf_proved : PspS4Leaf :=
  pspS4Leaf_of_leaves s4VertexModelLeaf_proved s4LinkModelLeaf_proved

end Final

end CFSG.ClassicalInvolution.Q3.Q3AM
