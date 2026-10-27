module

public import CFSG.ClassicalInvolution.Q3.Q3TIYFinal
public import CFSG.ClassicalInvolution.Q3.Q3TIYMf1
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk1
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk5
public import CFSG.ClassicalInvolution.Q3.Q3TY6

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIY


theorem twinYType3_of_odd3 (h3 : Q3W.OddThreeFreeInput) : Q3TY.TwinYType3On TwinRowLarge3 :=
  twinYType3_large_of_model h3 (fun _ _ h => twinMFCommutantOn3_large h)
    (fun _ _ h => twinRank3Model_large h) smallNoThree3

end CFSG.ClassicalInvolution.Q3.Q3TIY
