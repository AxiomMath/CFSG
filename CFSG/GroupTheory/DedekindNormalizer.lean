module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem inf_sup_eq_sup_inf_of_le_normalizer {S T U : Subgroup G} (hSU : S ≤ U)
    (hS : S ≤ Subgroup.normalizer (T : Set G)) : U ⊓ (S ⊔ T) = S ⊔ (U ⊓ T) := by
  have hS' : S ≤ Subgroup.normalizer (((U ⊓ T : Subgroup G) : Set G)) :=
    (le_inf (hSU.trans Subgroup.le_normalizer) hS).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  apply SetLike.coe_injective
  rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right S T hS,
    Subgroup.coe_mul_of_left_le_normalizer_right S (U ⊓ T) hS', inf_comm U T,
    Subgroup.mul_inf_assoc S T U hSU, Set.inter_comm]

end CFSG.GroupTheory
