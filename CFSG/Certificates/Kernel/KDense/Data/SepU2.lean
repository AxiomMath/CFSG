module

public import CFSG.Certificates.Kernel.KDense.Data.SepData

public section

set_option maxRecDepth 200000

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem u12 : Nat.beq (uVec U (nat_lit 12)) (uFromUT UT (nat_lit 12)) = true := by quickRfl
theorem u13 : Nat.beq (uVec U (nat_lit 13)) (uFromUT UT (nat_lit 13)) = true := by quickRfl
theorem u14 : Nat.beq (uVec U (nat_lit 14)) (uFromUT UT (nat_lit 14)) = true := by quickRfl
theorem u15 : Nat.beq (uVec U (nat_lit 15)) (uFromUT UT (nat_lit 15)) = true := by quickRfl
theorem u16 : Nat.beq (uVec U (nat_lit 16)) (uFromUT UT (nat_lit 16)) = true := by quickRfl
theorem u17 : Nat.beq (uVec U (nat_lit 17)) (uFromUT UT (nat_lit 17)) = true := by quickRfl

end CFSG.KD.KDS

end
