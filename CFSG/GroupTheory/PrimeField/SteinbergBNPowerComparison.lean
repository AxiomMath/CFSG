module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.GroupTheory.PrimeField

variable {G : Type*} [Group G]

theorem eq_one_of_pow_eq_one_of_coprime {U : Subgroup G} {w : G} (hw : w ∈ U) {m : ℕ}
    (hcop : Nat.Coprime (Nat.card U) m) (h : w ^ m = 1) : w = 1 := by
  have hu : (⟨w, hw⟩ : U) ^ m = 1 := Subtype.ext (by simpa using h)
  have h1 : orderOf (⟨w, hw⟩ : U) ∣ Nat.gcd (Nat.card U) m :=
    Nat.dvd_gcd (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one hu)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact congrArg Subtype.val h1

end CFSG.GroupTheory.PrimeField
