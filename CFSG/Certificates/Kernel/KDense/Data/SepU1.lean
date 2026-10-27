module

public import CFSG.Certificates.Kernel.KDense.Data.SepData

public section

set_option maxRecDepth 200000

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem u6 : Nat.beq (uVec U (nat_lit 6)) (uFromUT UT (nat_lit 6)) = true := by quickRfl
theorem u7 : Nat.beq (uVec U (nat_lit 7)) (uFromUT UT (nat_lit 7)) = true := by quickRfl
theorem u8 : Nat.beq (uVec U (nat_lit 8)) (uFromUT UT (nat_lit 8)) = true := by quickRfl
theorem u9 : Nat.beq (uVec U (nat_lit 9)) (uFromUT UT (nat_lit 9)) = true := by quickRfl
theorem u10 : Nat.beq (uVec U (nat_lit 10)) (uFromUT UT (nat_lit 10)) = true := by quickRfl
theorem u11 : Nat.beq (uVec U (nat_lit 11)) (uFromUT UT (nat_lit 11)) = true := by quickRfl

end CFSG.KD.KDS

end
