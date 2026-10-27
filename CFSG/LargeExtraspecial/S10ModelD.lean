module

public import CFSG.LargeExtraspecial.S10ModelB

public section

namespace CFSG.LargeExtraspecial.S10

theorem card_SL2 : Nat.card SL2 = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Γ₂ : Nat.card Γ₂ = 6 := by
  rw [← card_SL2]
  refine Nat.card_congr
    { toFun := fun γ => (γ : Gm).2
      invFun := fun B => ⟨(1, B), mem_Γ₂.mpr rfl⟩
      left_inv := fun γ => Subtype.ext (Prod.ext (mem_Γ₂.mp γ.2).symm rfl)
      right_inv := fun B => rfl }

theorem card_Γ₁ : Nat.card Γ₁ = 6 := by
  rw [← card_SL2]
  refine Nat.card_congr
    { toFun := fun γ => (γ : Gm).1
      invFun := fun A => ⟨(A, 1), mem_Γ₁.mpr rfl⟩
      left_inv := fun γ => Subtype.ext (Prod.ext rfl (mem_Γ₁.mp γ.2).symm)
      right_inv := fun A => rfl }

theorem eq_one_of_mem_Γ₁_of_mem_Γ₂ {γ : Gm} (h1 : γ.2 = 1) (h2 : γ.1 = 1) : γ = 1 :=
  Prod.ext h2 h1

theorem eq_mul_of_factors (γ : Gm) : γ = ((γ.1, 1) : Gm) * ((1, γ.2) : Gm) := by
  refine Prod.ext ?_ ?_ <;> simp

theorem conj_τ₂_ne : ∀ s : Gm, s.1 = 1 → s ^ 3 = 1 → s ≠ 1 → s * τ₂ * s⁻¹ ≠ τ₂ := by
  decide +kernel

end CFSG.LargeExtraspecial.S10
