module

public import CFSG.Certificates.Kernel.KDense.Data.SepData

public section

set_option maxRecDepth 200000

namespace CFSG.KD.KDS

open CFSG.KC CFSG.KC.KDense

theorem u18 : Nat.beq (uVec U (nat_lit 18)) (uFromUT UT (nat_lit 18)) = true := by quickRfl
theorem u19 : Nat.beq (uVec U (nat_lit 19)) (uFromUT UT (nat_lit 19)) = true := by quickRfl
theorem u20 : Nat.beq (uVec U (nat_lit 20)) (uFromUT UT (nat_lit 20)) = true := by quickRfl
theorem u21 : Nat.beq (uVec U (nat_lit 21)) (uFromUT UT (nat_lit 21)) = true := by quickRfl
theorem u22 : Nat.beq (uVec U (nat_lit 22)) (uFromUT UT (nat_lit 22)) = true := by quickRfl
theorem u23 : Nat.beq (uVec U (nat_lit 23)) (uFromUT UT (nat_lit 23)) = true := by quickRfl

end CFSG.KD.KDS

end
