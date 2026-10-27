module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

theorem card_eq_prime_add_one_of_fixedPoints_eq_singleton
    {p : ℕ} [Fact p.Prime]
    {P X : Type*} [Group P] [Finite X] [Nontrivial X] [MulAction P X]
    (hP : IsPGroup p P) (x0 : X)
    (hfixed : MulAction.fixedPoints P X = ({x0} : Set X))
    (hcard : Nat.card X ≤ p + 1) : Nat.card X = p + 1 := by
  have hmod := hP.card_modEq_card_fixedPoints X
  rw [hfixed] at hmod
  have hfix1 : Nat.card ({x0} : Set X) = 1 := Nat.card_of_subsingleton ⟨x0, rfl⟩
  rw [hfix1] at hmod
  have hlt : 1 < Nat.card X := Finite.one_lt_card
  have hdvd : p ∣ Nat.card X - 1 :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ Nat.card X)).mp hmod.symm
  have hpos : 0 < Nat.card X - 1 := by omega
  have hle : Nat.card X - 1 ≤ p := by omega
  have heq : Nat.card X - 1 = p := le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  omega

end CFSG
