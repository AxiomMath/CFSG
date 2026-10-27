module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Foundations.Basic

public section

namespace CFSG.CharacterTheory.SteinbergBY

open CFSG

theorem normal_subgroup_odd_core_containment {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : N.Normal) :
    ((pPrimeCore 2 N).map N.subtype).Normal ∧ (pPrimeCore 2 N).map N.subtype ≤ pPrimeCore 2 G ∧
      (pPrimeCore 2 N).map N.subtype = N ⊓ pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (pPrimeCore 2 N).map N.subtype = N ⊓ pPrimeCore 2 G := by
    rw [pPrimeCore_eq_piCore, pPrimeCore_eq_piCore]
    exact LocalCores.prime_set_core_normal_intersection _ hN
  refine ⟨?_, h ▸ inf_le_right, h⟩
  rw [h]
  exact Subgroup.normal_inf_normal N (pPrimeCore 2 G)

end CFSG.CharacterTheory.SteinbergBY
