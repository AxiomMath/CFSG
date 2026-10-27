module

public import CFSG.Certificates.Kernel.KDense.Data.SepData

public section

set_option maxRecDepth 200000

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem u0 : Nat.beq (uVec U (nat_lit 0)) (uFromUT UT (nat_lit 0)) = true := by quickRfl
theorem u1 : Nat.beq (uVec U (nat_lit 1)) (uFromUT UT (nat_lit 1)) = true := by quickRfl
theorem u2 : Nat.beq (uVec U (nat_lit 2)) (uFromUT UT (nat_lit 2)) = true := by quickRfl
theorem u3 : Nat.beq (uVec U (nat_lit 3)) (uFromUT UT (nat_lit 3)) = true := by quickRfl
theorem u4 : Nat.beq (uVec U (nat_lit 4)) (uFromUT UT (nat_lit 4)) = true := by quickRfl
theorem u5 : Nat.beq (uVec U (nat_lit 5)) (uFromUT UT (nat_lit 5)) = true := by quickRfl

end CFSG.KD.KDS

end
