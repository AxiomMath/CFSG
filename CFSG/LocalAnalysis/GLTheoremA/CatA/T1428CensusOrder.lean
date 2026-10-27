module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem orderA_one_two_pow_injective {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : orderA 1 (2 ^ a) = orderA 1 (2 ^ b)) : a = b := by
  have h1 : orderA 1 (2 ^ a) = 2 ^ a * ((2 ^ a) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.orderA_one_eq ha
  have h2 : orderA 1 (2 ^ b) = 2 ^ b * ((2 ^ b) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.orderA_one_eq hb
  have hodd1 : Odd ((2 ^ a) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one (a := a) (j := 2) ha
      (by norm_num)
  have hodd2 : Odd ((2 ^ b) ^ 2 - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatDistinct.odd_pow_two_pow_sub_one (a := b) (j := 2) hb
      (by norm_num)
  have hmul : 2 ^ a * ((2 ^ a) ^ 2 - 1) = 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
    rw [← h1, ← h2]
    exact h
  exact (CFSG.Quasithin.EmptyFaithfulMultiple.FFL.two_pow_mul_odd_inj hodd1 hodd2 hmul).1

end CFSG.LocalAnalysis.GLTheoremA
