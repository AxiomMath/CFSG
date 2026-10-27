module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

variable {n : ℕ} {F : Type} [Field F]

private theorem eq_one_of_forall_mulVec_eq {A : Matrix (Fin n) (Fin n) F}
    (h : ∀ v, A *ᵥ v = v) : A = 1 :=
  Matrix.ext_of_mulVec_single fun i => by rw [h, one_mulVec]

private theorem sub_dotProduct_eq_zero (g : GL (Fin n) F) {u : Fin n → F}
    (hu : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ u = u) (v : Fin n → F) :
    ((g : Matrix (Fin n) (Fin n) F) *ᵥ v - v) ⬝ᵥ u = 0 := by
  have h : ((g : Matrix (Fin n) (Fin n) F) *ᵥ v) ⬝ᵥ u = v ⬝ᵥ u := by
    conv_lhs => rw [← hu]
    rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, vecMul_vecMul, Units.inv_mul,
      vecMul_one, dotProduct_comm]
  rw [sub_dotProduct, h, sub_self]

private theorem mulVec_eq_add (g : GL (Fin n) F) (μ₁ : (Fin n → F) →ₗ[F] F)
    (hg : ∀ v, μ₁ v = 0 → (g : Matrix (Fin n) (Fin n) F) *ᵥ v = v) {v₀ : Fin n → F}
    (hv₀ : μ₁ v₀ = 1) (v : Fin n → F) :
    (g : Matrix (Fin n) (Fin n) F) *ᵥ v =
      v + μ₁ v • ((g : Matrix (Fin n) (Fin n) F) *ᵥ v₀ - v₀) := by
  have h := hg (v - μ₁ v • v₀) (by rw [map_sub, map_smul, hv₀, smul_eq_mul, mul_one, sub_self])
  rw [mulVec_sub, mulVec_smul] at h
  have h2 : (g : Matrix (Fin n) (Fin n) F) *ᵥ v =
      v - μ₁ v • v₀ + μ₁ v • ((g : Matrix (Fin n) (Fin n) F) *ᵥ v₀) := by
    rw [← h]
    abel
  rw [h2, smul_sub]
  abel

private theorem sub_dotProduct_eq_mul (g : GL (Fin n) F) (μ₂ : (Fin n → F) →ₗ[F] F)
    (hg : ∀ u, μ₂ u = 0 → ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ u = u)
    {u₀ : Fin n → F} (hu₀ : μ₂ u₀ = 1) (v u : Fin n → F) :
    ((g : Matrix (Fin n) (Fin n) F) *ᵥ v - v) ⬝ᵥ u =
      μ₂ u * (((g : Matrix (Fin n) (Fin n) F) *ᵥ v - v) ⬝ᵥ u₀) := by
  have h := sub_dotProduct_eq_zero g
    (hg (u - μ₂ u • u₀) (by rw [map_sub, map_smul, hu₀, smul_eq_mul, mul_one, sub_self])) v
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h
  exact h

private theorem card_le_of_forall_eq_one [Finite F] {P : GL (Fin n) F → Prop}
    (h : ∀ g, P g → g = 1) : Nat.card {g : GL (Fin n) F // P g} ≤ Nat.card F :=
  Nat.card_le_card_of_injective (fun _ => (0 : F)) fun g₁ g₂ _ =>
    Subtype.ext ((h _ g₁.2).trans (h _ g₂.2).symm)

theorem card_fix_ker_natDual_le [Finite F] (μ₁ μ₂ : (Fin n → F) →ₗ[F] F) :
    Nat.card {g : GL (Fin n) F //
      (∀ v, μ₁ v = 0 → (g : Matrix (Fin n) (Fin n) F) *ᵥ v = v) ∧
        ∀ u, μ₂ u = 0 → ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ u = u} ≤
      Nat.card F := by
  classical
  by_cases h₁ : ∃ v₀, μ₁ v₀ ≠ 0
  · by_cases h₂ : ∃ u₀, μ₂ u₀ ≠ 0
    · obtain ⟨v₀, hv₀⟩ := h₁
      obtain ⟨u₀, hu₀⟩ := h₂
      have hv₁ : μ₁ ((μ₁ v₀)⁻¹ • v₀) = 1 := by
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv₀]
      have hu₁ : μ₂ ((μ₂ u₀)⁻¹ • u₀) = 1 := by
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu₀]
      refine Nat.card_le_card_of_injective (fun g =>
        (((g.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ ((μ₁ v₀)⁻¹ • v₀) -
          (μ₁ v₀)⁻¹ • v₀) ⬝ᵥ ((μ₂ u₀)⁻¹ • u₀)) fun g₁ g₂ hg => ?_
      simp only at hg
      have ha : ((g₁.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ ((μ₁ v₀)⁻¹ • v₀) -
          (μ₁ v₀)⁻¹ • v₀ =
          ((g₂.1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ ((μ₁ v₀)⁻¹ • v₀) -
            (μ₁ v₀)⁻¹ • v₀ := by
        funext j
        rw [← dotProduct_single_one (_ - _) j, ← dotProduct_single_one (_ - _) j,
          sub_dotProduct_eq_mul g₁.1 μ₂ g₁.2.2 hu₁, sub_dotProduct_eq_mul g₂.1 μ₂ g₂.2.2 hu₁, hg]
      apply Subtype.ext
      apply Units.ext
      refine Matrix.ext_of_mulVec_single fun i => ?_
      rw [mulVec_eq_add g₁.1 μ₁ g₁.2.1 hv₁, mulVec_eq_add g₂.1 μ₁ g₂.2.1 hv₁, ha]
    · push Not at h₂
      refine card_le_of_forall_eq_one fun g hg => ?_
      have h := eq_one_of_forall_mulVec_eq fun u => hg.2 u (h₂ u)
      have h' : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
        simpa using congrArg Matrix.transpose h
      exact inv_eq_one.mp (Units.ext h')
  · push Not at h₁
    exact card_le_of_forall_eq_one fun g hg =>
      Units.ext (eq_one_of_forall_mulVec_eq fun v => hg.1 v (h₁ v))

end CFSG.ClassicalGroups.SpecialLinear
