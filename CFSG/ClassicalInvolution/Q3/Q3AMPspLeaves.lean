module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadLayerLeaf
public import CFSG.ClassicalInvolution.Q3.Q3AMPspC03
public import CFSG.ClassicalInvolution.Q3.Q3AMPspG05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

section Assembly


theorem pspLeaves_of_vertexS9 (h9 : PspVertexSLeaf9) : PspLeaves :=
  { vertexC := pspVertexC_proved
    layers := pspLayersSp4Leaf_proved
    vertexS9 := h9
    gen := pspLayerGen_proved }

theorem pspClose_of_vertexS9 (hM11 : Q3CH.M11OddAutInner3) (h9 : PspVertexSLeaf9) : PspClose :=
  pspClose_of_leaves hM11 (pspLeaves_of_vertexS9 h9)

theorem pspClose_of_vertexS9'
    (h9 : PspVertexSLeaf9) : PspClose :=
  pspClose_of_vertexS9 Q3CH.m11OddAutInner3 h9

end Assembly

end CFSG.ClassicalInvolution.Q3.Q3AM
