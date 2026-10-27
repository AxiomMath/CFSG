module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

variable {G : Type*} [Group G]

theorem lt_normalizer_inf_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {E Q : Subgroup G}
    (hE : IsPGroup p E) (hQE : Q ≤ E) (hQ : Q < E) :
    Q < Subgroup.normalizer (Q : Set G) ⊓ E := by
  have : Group.IsNilpotent E := hE.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := E)
  have hlt : Q.subgroupOf E < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hQ.ne (le_antisymm hQE (Subgroup.subgroupOf_eq_top.mp h))
  obtain ⟨x, hxN, hxH⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  have hxQ : (x : G) ∉ Q := fun h => hxH (Subgroup.mem_subgroupOf.mpr h)
  have hxNQ : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have key := Subgroup.mem_normalizer_iff.mp hxN
    constructor
    · intro hg
      have := (key ⟨g, hQE hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hg
      have hyE : (x : G) * g * (x : G)⁻¹ ∈ E := hQE hg
      have hgE : g ∈ E := by
        have hg' : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by
          simp [mul_assoc]
        rw [hg']
        exact E.mul_mem (E.mul_mem (E.inv_mem x.2) hyE) x.2
      have := (key ⟨g, hgE⟩).mpr (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp this
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hQE) ?_
  intro h
  apply hxQ
  have hxmem : (x : G) ∈ Subgroup.normalizer (Q : Set G) ⊓ E := ⟨hxNQ, x.2⟩
  rwa [← h] at hxmem

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
