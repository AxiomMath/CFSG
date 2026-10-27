module

public import CFSG.ClassicalInvolution.Q3.Q3TZSu4
public import CFSG.ClassicalInvolution.Q3.Q3TIYSu4Rank
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution.Q3.Q3W (OddThreeFreeInput)


theorem twinYNoCentral3_su4 : Q3TIY.TwinYNoCentral3On Q3TIY.TwinRowSU4 :=
  twinYNoCentral3_psu4

theorem twinYType3On_su4 (h3 : OddThreeFreeInput) : Q3TY.TwinYType3On Q3TIY.TwinRowSU4 :=
  Q3TIY.twinYType3On_su4_of_noCentral h3 twinYNoCentral3_su4

end CFSG.ClassicalInvolution.Q3.Q3TZ
