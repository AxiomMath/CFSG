module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase

public section

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.HardMathSupport.Foote.E27
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Enumeration

variable {G : Array Table} {P : Array (ℕ × ℕ)} {img : Array ℕ}
  {N : ℕ}

theorem factorization_two_pow_mul (k m : ℕ) (hm : ¬ 2 ∣ m) :
    (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

end Enumeration

end CFSG.EvenSporadicStandard.YS14
