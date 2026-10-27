module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.EvenSporadicStandard.HypOne

theorem two_pow_factorization_eq {c k b : ℕ} (hc : c = 2 ^ k * b) (hb : ¬ 2 ∣ b) :
    2 ^ c.factorization 2 = 2 ^ k := by
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero 2)
  rw [hc, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hb, add_zero]

end CFSG.EvenSporadicStandard.HypOne
