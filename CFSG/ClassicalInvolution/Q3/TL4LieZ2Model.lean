module

public import CFSG.ClassicalInvolution.Q3.TL4LieZ2L33
public import CFSG.ClassicalInvolution.Q3.TL4LieZ2M11

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem lieKindZ2Model_proved : LieKindZ2Model := by
  intro X _ _ Φ c hc hsec hshape
  rcases hc with rfl | rfl
  · exact LieZ2.linkZ2Model_l33 hsec hshape
  · exact LieZ2.linkZ2Model_m11 hsec hshape

end CFSG.ClassicalInvolution.Q3.TL4
