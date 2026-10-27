module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

open scoped commutatorElement

theorem isMulCommutative_of_card_le_four {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 4) : IsMulCommutative G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcases : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · exact (isCyclic_of_card_dvd_prime (p := 2)
      (by simpa [h1] using (show 1 ∣ 2 by norm_num))).isMulCommutative
  · exact (isCyclic_of_card_dvd_prime (p := 2)
      (by simpa [h2] using (show 2 ∣ 2 by norm_num))).isMulCommutative
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (isCyclic_of_prime_card (p := 3) h3).isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
      (by simpa [h4] using (show 4 = 2 ^ 2 by norm_num))

end CFSG
