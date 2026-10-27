module

public import Mathlib.GroupTheory.Focal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] (P : Subgroup G)

def focalGeneratorSet : Set G :=
  {z | ∃ x ∈ P, ∃ g : G, g⁻¹ * x * g ∈ P ∧ z = x⁻¹ * (g⁻¹ * x * g)}

theorem mem_focalGeneratorSet {z : G} :
    z ∈ focalGeneratorSet P ↔ ∃ x ∈ P, ∃ g : G, g⁻¹ * x * g ∈ P ∧ z = x⁻¹ * (g⁻¹ * x * g) :=
  Iff.rfl

theorem focalGeneratorSet_subset : focalGeneratorSet P ⊆ (P : Set G) := by
  rintro z ⟨x, hx, g, hy, rfl⟩
  exact P.mul_mem (P.inv_mem hx) hy

theorem focalGeneratorSet_eq :
    focalGeneratorSet P = {z : G | z ∈ P ∧ ∃ x ∈ P, ∃ u : G, z = ⁅x, u⁆} := by
  ext z
  rw [mem_focalGeneratorSet]
  constructor
  · rintro ⟨x, hx, g, hy, rfl⟩
    refine ⟨P.mul_mem (P.inv_mem hx) hy, x⁻¹, P.inv_mem hx, g⁻¹, ?_⟩
    rw [commutatorElement_def]
    group
  · rintro ⟨hz, x, hx, u, rfl⟩
    refine ⟨x⁻¹, P.inv_mem hx, u⁻¹, ?_, ?_⟩
    · have h : (u⁻¹)⁻¹ * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by
        rw [commutatorElement_def]; group
      rw [h]
      exact P.mul_mem (P.inv_mem hx) hz
    · rw [commutatorElement_def]; group

theorem closure_focalGeneratorSet : closure (focalGeneratorSet P) = focalSubgroup P := by
  rw [focalGeneratorSet_eq, focalSubgroup_def]

theorem subgroupOf_closure_focalGeneratorSet :
    (closure (focalGeneratorSet P)).subgroupOf P = focalSubgroupOf P := by
  rw [closure_focalGeneratorSet, focalSubgroupOf_def]

instance normal_focalGeneratorSet_subgroupOf :
    ((closure (focalGeneratorSet P)).subgroupOf P).Normal := by
  rw [subgroupOf_closure_focalGeneratorSet]
  infer_instance

theorem commutator_le_closure_focalGeneratorSet : ⁅P, P⁆ ≤ closure (focalGeneratorSet P) := by
  rw [closure_focalGeneratorSet]
  exact commutator_le_focalSubgroup P

theorem closure_focalGeneratorSet_le_inf :
    closure (focalGeneratorSet P) ≤ P ⊓ _root_.commutator G := by
  rw [closure_focalGeneratorSet]
  exact le_inf (focalSubgroup_le P) (focalSubgroup_le_commutator P)

instance isMulCommutative_quotient_focalGeneratorSet :
    IsMulCommutative (P ⧸ (closure (focalGeneratorSet P)).subgroupOf P) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have hmem : ⁅a, b⁆ ∈ (closure (focalGeneratorSet P)).subgroupOf P := by
        rw [subgroupOf_closure_focalGeneratorSet]
        exact commutator_le_focalSubgroupOf P
          (commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
      have h1 : (QuotientGroup.mk' ((closure (focalGeneratorSet P)).subgroupOf P)) ⁅a, b⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 hmem
      rw [map_commutatorElement] at h1
      simpa using commutatorElement_eq_one_iff_mul_comm.1 h1

end CFSG.FeitThompson
