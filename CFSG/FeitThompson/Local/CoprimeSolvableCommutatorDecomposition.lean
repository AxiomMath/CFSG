module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.CoprimeDisplacementFixedInDerived
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

section Invariance

variable {A V : Type*} [Group A] [Group V]

private theorem isInvariantSubgroup_of_forall_apply_mem {ρ : A →* MulAut V} {N : Subgroup V}
    (h : ∀ (b : A) (v : V), v ∈ N → ρ b v ∈ N) : IsInvariantSubgroup ρ N := by
  refine isInvariantSubgroup_iff_forall_map_eq.2 fun b => le_antisymm ?_ ?_
  · rintro x ⟨v, hv, rfl⟩
    exact h b v hv
  · intro v hv
    refine ⟨ρ b⁻¹ v, h b⁻¹ v hv, ?_⟩
    change ρ b (ρ b⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

variable (A V) [MulDistribMulAction A V]

theorem toMulAut_apply_eq_smul (a : A) (v : V) :
    MulDistribMulAction.toMulAut A V a v = a • v := rfl

theorem fixedPoints_subgroup_toMulAut_range :
    FixedPoints.subgroup (MulDistribMulAction.toMulAut A V).range V
      = FixedPoints.subgroup A V := by
  ext v
  rw [mem_fixedPoints_range_iff, FixedPoints.mem_subgroup]
  simp only [toMulAut_apply_eq_smul]

theorem isInvariantSubgroup_smulDisplacementSubgroup :
    IsInvariantSubgroup (MulDistribMulAction.toMulAut A V) (smulDisplacementSubgroup A V) :=
  isInvariantSubgroup_of_forall_apply_mem fun b _ hv => smul_mem_smulDisplacementSubgroup b hv

end Invariance

section Main

variable (A V : Type*) [Group A] [Group V] [MulDistribMulAction A V]
  [Finite A] [Finite V] [Group.IsSolvable A] [Group.IsSolvable V]

theorem exists_mem_smulDisplacementSubgroup_mul_mem_fixedPoints
    (hcop : (Nat.card A).Coprime (Nat.card V)) (v : V) :
    ∃ w ∈ smulDisplacementSubgroup A V, ∃ c ∈ FixedPoints.subgroup A V, v = w * c := by
  obtain ⟨n, hnN, hfix⟩ := exists_mem_forall_apply_mul_eq
    (isInvariantSubgroup_smulDisplacementSubgroup A V) hcop
    (v := v) fun b => inv_mul_smul_mem_smulDisplacementSubgroup b v
  refine ⟨v * n⁻¹ * v⁻¹, ?_, v * n, (FixedPoints.mem_subgroup A V _).2 hfix, by group⟩
  exact (smulDisplacementSubgroup_normal (A := A) (V := V)).conj_mem _ (inv_mem hnN) v

theorem smulDisplacementSubgroup_sup_fixedPoints_subgroup
    (hcop : (Nat.card A).Coprime (Nat.card V)) :
    smulDisplacementSubgroup A V ⊔ FixedPoints.subgroup A V = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨w, hw, c, hc, rfl⟩ :=
    exists_mem_smulDisplacementSubgroup_mul_mem_fixedPoints A V hcop v
  exact mul_mem (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right hc)

theorem coe_smulDisplacementSubgroup_mul_coe_fixedPoints_subgroup
    (hcop : (Nat.card A).Coprime (Nat.card V)) :
    (smulDisplacementSubgroup A V : Set V) * (FixedPoints.subgroup A V : Set V) = Set.univ := by
  rw [← Subgroup.normal_mul, smulDisplacementSubgroup_sup_fixedPoints_subgroup A V hcop,
    Subgroup.coe_top]

end Main

section MonoidHomVersion

variable {A V : Type*} [Group A] [Group V] (ρ : A →* MulAut V)

theorem normal_closure_setOf_inv_mul_apply :
    (Subgroup.closure {x : V | ∃ (a : A) (v : V), v⁻¹ * ρ a v = x}).Normal := by
  let _ : MulDistribMulAction A V := MulDistribMulAction.compHom V ρ
  have h : smulDisplacementSubgroup A V
      = Subgroup.closure {x : V | ∃ (a : A) (v : V), v⁻¹ * ρ a v = x} :=
    smulDisplacementSubgroup_eq_closure
  rw [← h]
  infer_instance

theorem isInvariantSubgroup_closure_setOf_inv_mul_apply :
    IsInvariantSubgroup ρ (Subgroup.closure {x : V | ∃ (a : A) (v : V), v⁻¹ * ρ a v = x}) := by
  let _ : MulDistribMulAction A V := MulDistribMulAction.compHom V ρ
  have h : smulDisplacementSubgroup A V
      = Subgroup.closure {x : V | ∃ (a : A) (v : V), v⁻¹ * ρ a v = x} :=
    smulDisplacementSubgroup_eq_closure
  refine isInvariantSubgroup_of_forall_apply_mem fun b v hv => ?_
  rw [← h] at hv ⊢
  exact smul_mem_smulDisplacementSubgroup b hv

theorem closure_setOf_inv_mul_apply_sup_fixedPoints_range
    [Finite A] [Finite V] [Group.IsSolvable A] [Group.IsSolvable V]
    (hcop : (Nat.card A).Coprime (Nat.card V)) :
    Subgroup.closure {x : V | ∃ (a : A) (v : V), v⁻¹ * ρ a v = x}
        ⊔ FixedPoints.subgroup ρ.range V = ⊤ := by
  let _ : MulDistribMulAction A V := MulDistribMulAction.compHom V ρ
  have h : smulDisplacementSubgroup A V
      = Subgroup.closure {x : V | ∃ (a : A) (v : V), v⁻¹ * ρ a v = x} :=
    smulDisplacementSubgroup_eq_closure
  have hf : FixedPoints.subgroup ρ.range V = FixedPoints.subgroup A V := by
    ext w
    rw [mem_fixedPoints_range_iff, FixedPoints.mem_subgroup]
    exact Iff.rfl
  rw [← h, hf]
  exact smulDisplacementSubgroup_sup_fixedPoints_subgroup A V hcop

end MonoidHomVersion

end CFSG.FeitThompson
