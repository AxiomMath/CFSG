module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup

variable {C : Type*} [Group C] [Finite C]

omit [Finite C] in
theorem zpow_eq_one_or_self_aux {c : C} (hc : c * c = 1) (j : ℤ) : c ^ j = 1 ∨ c ^ j = c := by
  rcases Int.even_or_odd' j with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hc, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hc, one_zpow, one_mul, zpow_one]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
