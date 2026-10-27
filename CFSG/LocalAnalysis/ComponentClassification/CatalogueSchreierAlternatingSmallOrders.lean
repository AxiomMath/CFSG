module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem commutative_of_card_le_four {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G ≤ 4) : IsMulCommutative G := by
  have hpositive : 0 < Nat.card G := Nat.card_pos
  have hcases : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by
    omega
  rcases hcases with hcard | hcard | hcard | hcard
  · let : IsCyclic G := isCyclic_of_card_dvd_prime (p := 2) (by rw [hcard]; norm_num)
    infer_instance
  · let : IsCyclic G := isCyclic_of_card_dvd_prime (p := 2) (by rw [hcard])
    infer_instance
  · let : IsCyclic G := isCyclic_of_card_dvd_prime (p := 3) (by rw [hcard])
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard

theorem solvable_of_card_le_four {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G ≤ 4) : Group.IsSolvable G := by
  exact Group.isSolvable_of_comm (commutative_of_card_le_four hcard).is_comm.comm

end CFSG.ComponentClassification.CatalogueSchreierAlternating
