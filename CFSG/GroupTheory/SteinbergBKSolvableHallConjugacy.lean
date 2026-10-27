module

public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory.SteinbergBK

universe u

theorem solvable_hall_conjugacy {G : Type u} [Group G] [Finite G] (hG : Group.IsSolvable G)
    {π : Set Nat.Primes} {H K : Subgroup G} (hH : IsHallSubgroup π H)
    (hK : IsHallSubgroup π K) : ∃ g : G, conjugate H g = K := by
  obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hG hH hK
  refine ⟨g⁻¹, ?_⟩
  rw [conjugate, inv_inv, hg]

end CFSG.GroupTheory.SteinbergBK
