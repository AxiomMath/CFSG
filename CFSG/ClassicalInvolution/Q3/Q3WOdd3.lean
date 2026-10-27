module

public import CFSG.ClassicalInvolution.Q3.Q3NHIntr
public import CFSG.ClassicalInvolution.Q3.Q3WARow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W


theorem oddThreeFreeInput_proved : OddThreeFreeInput :=
  fun _ _ _ _ _ _ hR => Q3NH.localOddThreeFree3_of_intrinsic_at hR.cls hR.intr hR.setup.1

end CFSG.ClassicalInvolution.Q3.Q3W
