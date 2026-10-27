module

public import CFSG.ClassicalInvolution.Q3.Q3OFStmt

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
open scoped MatrixGroups commutatorElement

section Algebra

variable {C : Type} [Group C]

theorem exists_mul_of_mem_sup_of_commutes {A B : Subgroup C}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : C} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let T : Subgroup C :=
    { carrier := {y | ∃ a ∈ A, ∃ b ∈ B, y = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h a ha b hb]
          _ = a⁻¹ * b⁻¹ := mul_inv_rev b a }
  have hle : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx

end Algebra

end CFSG.ClassicalInvolution.Q3.Q3OF
