module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Ivk95Sp4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open scoped commutatorElement

section Cfg

variable {J : Type} [Group J] [Finite J] {z : J}

theorem false_of_simple_between (h : Ivk95Cfg z) {S : Subgroup J} (hS : IsSimpleGroup ↥S)
    (hKS : Ez z ≤ S) (hSC : S ≤ centralizer ({z} : Set J)) : False := by
  have hzS : z ∈ S := hKS h.mem
  have hz1 : z ≠ 1 := by
    intro h1
    have := h.ord
    rw [h1, orderOf_one] at this
    omega
  have hcomm : ∀ g : ↥S, (g : J) * z = z * (g : J) := fun g =>
    mem_centralizer_singleton_iff.mp (hSC g.2)
  have hN : ((Ez z).subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    exact h.conj_mem (g : J) (hcomm g) n hn
  have hzN : (⟨z, hzS⟩ : ↥S) ∈ (Ez z).subgroupOf S := h.mem
  have hz1' : (⟨z, hzS⟩ : ↥S) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥S) with hc | hc
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Ez z).subgroupOf S) with hb | ht
    · rw [hb] at hzN
      exact hz1' hzN
    · have hKS' : ∀ s : ↥S, (s : J) ∈ Ez z := fun s => by
        have : s ∈ (Ez z).subgroupOf S := by rw [ht]; exact mem_top s
        exact this
      have hzc : (⟨z, hzS⟩ : ↥S) ∈ center ↥S := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (h.central _ (hKS' g))
      rw [hc] at hzc
      exact hz1' hzc
  · apply h.not_solvable
    refine Group.isSolvable_of_comm fun a b => ?_
    have hb' : (⟨(b : J), hKS b.2⟩ : ↥S) ∈ center ↥S := by rw [hc]; exact mem_top _
    have h1 := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hb') ⟨(a : J), hKS a.2⟩)
    exact Subtype.ext h1

end Cfg

section Components

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_of_normalizes {A B C : Subgroup G} (hAB : A ≤ B)
    (hA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A) (hB : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B) :
    (A.subgroupOf C).IsSubnormal := by
  have hBn : (B.subgroupOf C).Normal := ⟨fun n hn g => hB (g : G) g.2 (n : G) hn⟩
  refine Subgroup.IsSubnormal.step _ (B.subgroupOf C) (Subgroup.subgroupOf_mono C hAB)
    hBn.isSubnormal ⟨fun n hn g => ?_⟩
  exact hA ((g : ↥C) : G) g.2 ((n : ↥C) : G) hn

theorem not_forall_comm_of_isQuasisimple {A : Subgroup G} (hA : IsQuasisimple ↥A) :
    ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro hc
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hA
    (Group.isSolvable_of_comm fun a b => Subtype.ext (hc _ a.2 _ b.2))

variable [Finite G]

theorem eq_or_commute_of_isComponent {A B C : Subgroup G} (hAC : A ≤ C) (hBC : B ≤ C)
    (hA : IsComponent (A.subgroupOf C)) (hB : IsComponent (B.subgroupOf C)) :
    A = B ∨ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  rcases LocalCores.distinct_components_commute hA hB with h | h
  · left
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hAC, inf_eq_left.mpr hBC] at this
  · right
    intro a ha b hb
    have h1 : ⁅(⟨a, hAC ha⟩ : ↥C), ⟨b, hBC hb⟩⁆ ∈ ⁅A.subgroupOf C, B.subgroupOf C⁆ :=
      Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact congrArg Subtype.val h1

end Components

end Ivk95Sp4

end CFSG.GH74.GLS.IVK.Proofs2
