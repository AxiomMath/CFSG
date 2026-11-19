module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

open scoped commutatorElement

theorem isMulCommutative_of_card_le_four {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsMulCommutative G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcases : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · exact (isCyclic_of_card_dvd_prime (p := 2)
      (by simp [h1])).isMulCommutative
  · exact (isCyclic_of_card_dvd_prime (p := 2)
      (by simp [h2])).isMulCommutative
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (isCyclic_of_prime_card (p := 3) h3).isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (by simp [h4])

end CFSG
