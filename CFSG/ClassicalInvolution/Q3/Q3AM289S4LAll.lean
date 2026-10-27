module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU04
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LOdd01
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LMin01
public import CFSG.ClassicalInvolution.AschTight.S19KUni
public import CFSG.ClassicalInvolution.AschTight.S19KUniFL
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Gram
public import CFSG.ClassicalInvolution.Q3.Q3NMSl23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM


theorem s4LinkModelLeaf_proved : S4LinkModelLeaf :=
  ⟨s4LinkModelLeafAt_su4, s4LinkModelLeafAt_odd3, s4LinkModelLeafAt_minus4⟩

end CFSG.ClassicalInvolution.Q3.Q3AM
