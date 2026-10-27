module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem exists_mem_normalizer_not_mem [Finite G] {P H : Subgroup G} (hP : IsPGroup 2 ↥P)
    (hHP : H < P) : ∃ g ∈ P, g ∉ H ∧ g ∈ normalizer (H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent
  have hlt : H.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact absurd htop (not_le_of_gt hHP)
  have h1 := hnc _ hlt
  obtain ⟨g, hg1, hg2⟩ := IsConcreteLE.exists_of_lt h1
  refine ⟨g.1, g.2, hg2, ?_⟩
  have h2 : g ∈ (normalizer (H : Set G)).subgroupOf P := by
    rw [Subgroup.subgroupOf_normalizer_eq hHP.le]
    exact hg1
  exact h2

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
