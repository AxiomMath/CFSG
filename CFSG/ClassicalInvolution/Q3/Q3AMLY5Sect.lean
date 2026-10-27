module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Stmt
public import CFSG.ClassicalInvolution.Q3.Q3AMLY3Thin
public import CFSG.ClassicalInvolution.Q3.Q3AMLY4G

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

section Section


theorem e2Y_proved : SectionLeafY := by
  intro G _ _ _ Ω K J S R T W z t h
  rcases layer_shape_of_thinY h.bad h.hint h.noTri h.thin with hT | hL3 | hM11
  · exact absurd hT (c26_1Y h.bad h.hint h.noTri)
  · exact Or.inl hL3
  · exact Or.inr hM11

end Section

end CFSG.ClassicalInvolution.Q3.Q3AM
