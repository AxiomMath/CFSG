module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem exists_mem_center_orderOf_eq_two {T : Type*} [Group T] [Finite T] (hT : IsPGroup 2 T)
    [Nontrivial T] : ∃ z ∈ center T, orderOf z = 2 := by
  obtain ⟨n, hn0, hncard⟩ :=
    (hT.to_subgroup (center T)).nontrivial_iff_card.mp hT.center_nontrivial
  have hdvd : 2 ∣ Nat.card (center T) := by
    rw [hncard]
    exact dvd_pow_self 2 hn0.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩

end CFSG.GroupTheory.SmallFixedTwoGroup
