module

public import CFSG.ClassicalInvolution.Q3.TL4E3E4Perf
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4All

public section

namespace CFSG.ClassicalInvolution.Q3.TL4


theorem tightE4Perfect_proved : TightE4Perfect :=
  tightE4Perfect_of_acts3 fun _ _ _ hM => e4QuatActs3_of_exLie hM

end CFSG.ClassicalInvolution.Q3.TL4
