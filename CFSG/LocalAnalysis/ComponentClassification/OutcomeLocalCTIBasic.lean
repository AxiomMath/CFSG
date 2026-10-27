module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup

theorem not_isComponent_of_selfCentralizing {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {R : Subgroup G} (hRn : R.Normal) (hRp : IsPGroup p R)
    (hcen : centralizer (R : Set G) ≤ R) (K : Subgroup G) : ¬ CFSG.IsComponent K := by
  intro hK
  have hKR : K ≤ R := by
    rcases CFSG.LocalCores.component_normal_subgroup hK hRn with h | h
    · exact h
    · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans hcen
  have hsolv : Group.IsSolvable R := by
    have := hRp.isNilpotent
    infer_instance
  have : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (inclusion_injective hKR)
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable (G := K) ‹_›

theorem not_isComponent_of_le {G : Type*} [Group G] {C Q : Subgroup G} [Finite C] {p : ℕ}
    [Fact p.Prime] (hQC : Q ≤ C) (hQp : IsPGroup p Q)
    (hnorm : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hcen : ∀ c ∈ C, (∀ q ∈ Q, c * q = q * c) → c ∈ Q) (K : Subgroup C) :
    ¬ CFSG.IsComponent K := by
  refine not_isComponent_of_selfCentralizing (R := Q.subgroupOf C) ?_
    (hQp.comap_of_injective C.subtype C.subtype_injective) ?_ K
  · refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    exact hnorm g g.2 x hx
  · intro c hc
    rw [mem_subgroupOf]
    refine hcen c c.2 fun q hq => ?_
    have h := mem_centralizer_iff.mp hc ⟨q, hQC hq⟩
      (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hq)
    exact (congrArg Subtype.val h).symm

end CFSG.ComponentClassification.OutcomeLocal
