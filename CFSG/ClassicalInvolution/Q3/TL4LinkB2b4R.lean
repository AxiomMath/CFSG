module

public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

theorem quatAutFacts_of_four_le {r : ℕ} (hr : 4 ≤ r) : QuatAutFacts r :=
  QuatAutFacts.of_three_le (by omega)

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

