module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Gen
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup CFSG CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Extract

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_component_noncentral_of_Em {N A : Subgroup G} (hAN : A ≤ N)
    (hAE : ¬ A ≤ centralizer (Em N : Set G)) :
    ∃ J : Subgroup ↥N, IsComponent J ∧ ¬ A.subgroupOf N ≤ centralizer (J : Set ↥N) := by
  have h : ⁅layer ↥N, A.subgroupOf N⁆ ≠ ⊥ := by
    intro hbot
    apply hAE
    have hle : layer ↥N ≤ centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro e ⟨l, hl, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hle hl) ⟨a, hAN ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    have h2 := congrArg Subtype.val h1
    simpa [Subgroup.coe_mul] using h2.symm
  exact exists_component_noncentral h

end Extract

section Image

variable {Y : Type} [Group Y] [Finite Y]

theorem not_le_centralizer_map {p : ℕ} (hp : p.Prime) {J X A : Subgroup Y} (hJ : IsComponent J)
    (hAX : A ≤ X) (hnc : ¬ A ≤ centralizer (J : Set Y)) :
    ¬ X.map (QuotientGroup.mk' (pCore p Y)) ≤
      centralizer ((J.map (QuotientGroup.mk' (pCore p Y)) : Subgroup (Y ⧸ pCore p Y)) :
        Set (Y ⧸ pCore p Y)) := by
  intro hle
  have : Fact p.Prime := ⟨hp⟩
  apply hnc
  refine hAX.trans ?_
  have hOJ := pCore_le_centralizer_component hp hJ
  have hxn : ∀ x ∈ X, x ∈ normalizer (J : Set Y) := by
    intro x hx
    refine mem_normalizer_of_image hp hJ ?_
    exact Subgroup.centralizer_le_normalizer _ (hle ⟨x, hx, rfl⟩)
  have hcomm : ⁅J, X⁆ ≤ centralizer (J : Set Y) := by
    refine Subgroup.commutator_le.mpr fun j hj x hx => ?_
    have hπ : QuotientGroup.mk' (pCore p Y) ⁅j, x⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp (hle ⟨x, hx, rfl⟩) _ ⟨j, hj, rfl⟩
    have hmem : ⁅j, x⁆ ∈ pCore p Y := (QuotientGroup.eq_one_iff _).mp hπ
    exact hOJ hmem
  exact le_centralizer_of_commutator_le_centralizer hJ.1.1 hcomm

end Image

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
