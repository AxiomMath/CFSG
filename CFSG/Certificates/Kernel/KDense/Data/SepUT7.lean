module

public import CFSG.Certificates.Kernel.KDense.Data.SepData

public section

set_option maxRecDepth 200000

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem ut7 : utRange CFSG.KD.KDF.OCT (nat_lit 14) (utSlice UT (nat_lit 7)) (Nat.mul (nat_lit 7) (nat_lit 16384)) =
  true := by quickRfl

end CFSG.KD.KDS

end
