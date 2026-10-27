module

public import CFSG.LieType.TitsSimplicity.Simplicity
public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace CFSG.LieType.Simplicity

open CFSG.LieType.TitsSimplicity

variable {G X : Type*} [Group G] [MulAction G X]

theorem isSimpleGroup_of_isPreprimitive_of_isSolvable_stabilizer [Nontrivial G]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] (hperf : Group.IsPerfect G) (x : X)
    (hsolv : Group.IsSolvable (MulAction.stabilizer G x)) : IsSimpleGroup G := by
  refine ⟨fun N hN => ?_⟩
  by_cases hN1 : N = ⊥
  · exact .inl hN1
  right
  have hfix : MulAction.fixedPoints N X ≠ Set.univ := by
    intro h
    apply hN1
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine eq_of_smul_eq_smul (α := X) fun y => ?_
    have hy : y ∈ MulAction.fixedPoints N X := h ▸ Set.mem_univ y
    rw [one_smul]
    exact hy ⟨g, hg⟩
  have htrans : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
  refine eq_top_of_sup_eq_top hperf hsolv (eq_top_iff.2 fun g _ => ?_)
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N x (g • x)
  have hstab : (n : G)⁻¹ * g ∈ MulAction.stabilizer G x := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hn, Subgroup.smul_def, inv_smul_smul]
  have e : g = (n : G) * ((n : G)⁻¹ * g) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right hstab)

end CFSG.LieType.Simplicity
