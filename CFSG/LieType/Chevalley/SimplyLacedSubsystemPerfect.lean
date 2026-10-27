module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public section

namespace CFSG.LieType.Chevalley.SLPerfect

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

section Certified


theorem xUnit_mem_commutator_subsystemGroup {A : Set (Fin τ.rank)} {i l : Fin τ.rank}
    (hi : i ∈ A) (hl : l ∈ A) (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) (c : K) :
    xUnit τ K i c ∈ ⁅subsystemGroup τ K A, subsystemGroup τ K A⁆ := by
  have hn : weylElt τ K l 1 ∈ subsystemGroup τ K A := weylElt_mem_subsystemGroup hl 1
  have key : xUnit τ K i c = (weylElt τ K l 1)⁻¹ * ⁅xUnit τ K l 1, xUnit τ K i c⁆ *
      (weylElt τ K l 1)⁻¹⁻¹ := by
    rw [(a2_simple_root_commutatorElement K hli hil 1 c).1, one_mul]
    group
  rw [key, conjugate_commutatorElement]
  exact Subgroup.commutator_mem_commutator
    (mul_mem (mul_mem (inv_mem hn) (xUnit_mem_subsystemGroup hl 1)) (inv_mem (inv_mem hn)))
    (mul_mem (mul_mem (inv_mem hn) (xUnit_mem_subsystemGroup hi c)) (inv_mem (inv_mem hn)))

theorem yUnit_mem_commutator_subsystemGroup {A : Set (Fin τ.rank)} {i l : Fin τ.rank}
    (hi : i ∈ A) (hl : l ∈ A) (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) (c : K) :
    yUnit τ K i c ∈ ⁅subsystemGroup τ K A, subsystemGroup τ K A⁆ := by
  have hn : weylElt τ K l 1 ∈ subsystemGroup τ K A := weylElt_mem_subsystemGroup hl 1
  have h := (a2_simple_root_commutatorElement K hli hil 1 (-c)).2
  rw [one_mul, neg_neg] at h
  have key : yUnit τ K i c = (weylElt τ K l 1)⁻¹ * ⁅yUnit τ K l 1, yUnit τ K i (-c)⁆ *
      (weylElt τ K l 1)⁻¹⁻¹ := by
    rw [h]
    group
  rw [key, conjugate_commutatorElement]
  exact Subgroup.commutator_mem_commutator
    (mul_mem (mul_mem (inv_mem hn) (yUnit_mem_subsystemGroup hl 1)) (inv_mem (inv_mem hn)))
    (mul_mem (mul_mem (inv_mem hn) (yUnit_mem_subsystemGroup hi (-c))) (inv_mem (inv_mem hn)))

theorem isPerfect_subsystemGroup_of_simplyLaced {A : Set (Fin τ.rank)}
    (hA : ∀ i ∈ A, ∃ l ∈ A, τ.cartan i l = -1 ∧ τ.cartan l i = -1) :
    Group.IsPerfect (subsystemGroup τ K A) := by
  have hle : subsystemGroup τ K A ≤ ⁅subsystemGroup τ K A, subsystemGroup τ K A⁆ := by
    conv_lhs => rw [subsystemGroup]
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨l, hl, hil, hli⟩ := hA i hi
      exact xUnit_mem_commutator_subsystemGroup hi hl hil hli c
    · obtain ⟨l, hl, hil, hli⟩ := hA i hi
      exact yUnit_mem_commutator_subsystemGroup hi hl hil hli c
  refine Subgroup.isPerfect_iff.2 (le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) hle)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

end Certified

end CFSG.LieType.Chevalley.SLPerfect
