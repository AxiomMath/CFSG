module
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import Mathlib.GroupTheory.Commutator.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable (G : Type*) [Group G]

theorem closure_setOf_inv_mul_inv_mul_mul_eq_commutator :
    Subgroup.closure {g : G | ∃ x y : G, x⁻¹ * y⁻¹ * x * y = g} = commutator G := by
  rw [commutator_def, ← closure_setOf_inv_mul_inv_mul_mul (⊤ : Subgroup G) ⊤]
  congr 1
  ext g
  simp

theorem characteristic_closure_setOf_inv_mul_inv_mul_mul :
    (Subgroup.closure {g : G | ∃ x y : G, x⁻¹ * y⁻¹ * x * y = g}).Characteristic := by
  rw [closure_setOf_inv_mul_inv_mul_mul_eq_commutator]
  infer_instance

theorem map_closure_setOf_inv_mul_inv_mul_mul_eq_self (ϕ : G ≃* G) :
    Subgroup.map ϕ.toMonoidHom (Subgroup.closure {g : G | ∃ x y : G, x⁻¹ * y⁻¹ * x * y = g}) =
      Subgroup.closure {g : G | ∃ x y : G, x⁻¹ * y⁻¹ * x * y = g} :=
  Subgroup.characteristic_iff_map_eq.mp (characteristic_closure_setOf_inv_mul_inv_mul_mul G) ϕ

theorem normal_closure_setOf_inv_mul_inv_mul_mul :
    (Subgroup.closure {g : G | ∃ x y : G, x⁻¹ * y⁻¹ * x * y = g}).Normal :=
  have := characteristic_closure_setOf_inv_mul_inv_mul_mul G
  Subgroup.normal_of_characteristic _

theorem isMulCommutative_quotient_commutator : IsMulCommutative (G ⧸ commutator G) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl

end CFSG.FeitThompson
