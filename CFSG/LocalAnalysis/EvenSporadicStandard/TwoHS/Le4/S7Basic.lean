module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem not_two_dvd_index_of_normalizer_le {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) (hN : normalizer (T : Set G) ≤ T) : ¬ 2 ∣ T.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  have hP : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
  have hnil : Group.IsNilpotent (P : Subgroup G) := hP.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := (P : Subgroup G))
  have hEq : T = P := by
    by_contra hne
    have hlt : T.subgroupOf P < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      apply hne
      refine le_antisymm hTP ?_
      intro x hx
      have : (⟨x, hx⟩ : (P : Subgroup G)) ∈ T.subgroupOf P := by rw [h]; trivial
      exact this
    obtain ⟨x, hx, hxn⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
    apply hxn
    have hxN : (x : G) ∈ normalizer (T : Set G) := by
      rw [mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact (mem_normalizer_iff.1 hx ⟨h, hTP hh⟩).1 hh
      · intro hh
        have hhP : h ∈ (P : Subgroup G) := by
          have h1 : (x : G) * h * (x : G)⁻¹ ∈ (P : Subgroup G) := hTP hh
          have h2 := (P : Subgroup G).mul_mem
            ((P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem x.2) h1) x.2
          simpa [mul_assoc] using h2
        exact (mem_normalizer_iff.1 hx ⟨h, hhP⟩).2 hh
    exact hN hxN
  subst hEq
  exact P.not_dvd_index

variable {G : Type*} [Group G]

end CFSG.EvenSporadicStandard.TwoHS
