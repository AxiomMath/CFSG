module

public import Mathlib.GroupTheory.GroupAction.Primitive

public section

namespace CFSG.GroupActions

open MulAction Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

theorem isPretransitive_of_normal_of_isPreprimitive [FaithfulSMul G X] [IsPreprimitive G X]
    [Nonempty X] {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) : IsPretransitive N X := by
  refine IsQuasiPreprimitive.isPretransitive_of_normal fun h => hN ?_
  rw [eq_bot_iff]
  intro n hn
  refine eq_of_smul_eq_smul (α := X) fun x => ?_
  have hx : x ∈ fixedPoints N X := h ▸ Set.mem_univ x
  rw [one_smul]
  exact hx ⟨n, hn⟩

theorem exists_mul_of_isPretransitive (N : Subgroup G) [IsPretransitive N X] (a : X) (g : G) :
    ∃ n ∈ N, ∃ h ∈ stabilizer G a, g = n * h := by
  obtain ⟨n, hn⟩ := exists_smul_eq N a (g • a)
  refine ⟨n, n.2, (n : G)⁻¹ * g, ?_, (mul_inv_cancel_left _ _).symm⟩
  rw [mem_stabilizer_iff, mul_smul, ← hn, Subgroup.smul_def, inv_smul_smul]

theorem mul_stabilizer_eq_univ (N : Subgroup G) [IsPretransitive N X] (a : X) :
    (N : Set G) * (stabilizer G a : Set G) = Set.univ := by
  refine Set.eq_univ_of_forall fun g => ?_
  obtain ⟨n, hn, h, hh, rfl⟩ := exists_mul_of_isPretransitive N a g
  exact Set.mul_mem_mul hn hh

end CFSG.GroupActions
