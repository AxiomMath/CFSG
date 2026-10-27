module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CentCore

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_mem_of_perfect {H J F N X : Subgroup G} (hJH : J ≤ H) (hFH : F ≤ H)
    (hXH : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hperf : ⁅J, J⁆ = J)
    (hNJ : ∀ n ∈ N, ∀ j ∈ J, ⁅n, j⁆ ∈ X) (hFJ : ∀ f ∈ F, ∀ j ∈ J, ⁅f, j⁆ ∈ N) :
    ∀ j ∈ J, ∀ f ∈ F, ⁅j, f⁆ ∈ X := by
  have hXn : (X.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hXH g g.2 n hn⟩
  let π : ↥H →* ↥H ⧸ X.subgroupOf H := QuotientGroup.mk' (X.subgroupOf H)
  set A : Subgroup (↥H ⧸ X.subgroupOf H) := (J.subgroupOf H).map π with hA
  set B : Subgroup (↥H ⧸ X.subgroupOf H) := (F.subgroupOf H).map π with hB
  set C : Subgroup (↥H ⧸ X.subgroupOf H) := (N.subgroupOf H).map π with hC
  have hAB : ⁅A, B⁆ ≤ C := by
    rw [hA, hB, ← Subgroup.map_commutator]
    apply Subgroup.map_mono
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    have h1 : ⁅(b : G), (a : G)⁆ ∈ N := hFJ _ hb _ ha
    have h2 : ((⁅a, b⁆ : ↥H) : G) = (⁅(b : G), (a : G)⁆)⁻¹ := by
      rw [commutatorElement_inv]
      rfl
    rw [h2]
    exact N.inv_mem h1
  have hCA : ⁅C, A⁆ = ⊥ := by
    rw [hC, hA, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [Subgroup.commutator_le]
    intro n hn j hj
    rw [Subgroup.mem_subgroupOf] at hn hj ⊢
    exact hNJ _ hn _ hj
  have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ :=
    le_antisymm ((Subgroup.commutator_mono hAB le_rfl).trans hCA.le) bot_le
  have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm B A]
    exact h1
  have hrot : ⁅⁅A, A⁆, B⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := A) (H₃ := B) h1 h2
  have hAA : ⁅A, A⁆ = A := by
    have hJ' : ⁅J.subgroupOf H, J.subgroupOf H⁆ = J.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH, hperf]
    rw [hA, ← Subgroup.map_commutator, hJ']
  have hAB' : ⁅A, B⁆ = ⊥ := by
    have := hrot
    rwa [hAA] at this
  intro j hj f hf
  have hjA : π ⟨j, hJH hj⟩ ∈ A :=
    Subgroup.mem_map_of_mem π (show (⟨j, hJH hj⟩ : ↥H) ∈ J.subgroupOf H from hj)
  have hfB : π ⟨f, hFH hf⟩ ∈ B :=
    Subgroup.mem_map_of_mem π (show (⟨f, hFH hf⟩ : ↥H) ∈ F.subgroupOf H from hf)
  have hmem : ⁅π ⟨j, hJH hj⟩, π ⟨f, hFH hf⟩⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator hjA hfB
  rw [hAB', Subgroup.mem_bot, ← map_commutatorElement] at hmem
  have := (QuotientGroup.eq_one_iff (N := X.subgroupOf H) _).1 hmem
  exact Subgroup.mem_subgroupOf.1 this

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CentCore
