module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LinearAlgebra

open Matrix

theorem ringEquiv_eq_refl_of_forall_exists_smul {F : Type*} [Field F] {n : ℕ}
    (A : GL (Fin n) F) (φ : F ≃+* F) {p₁ p₂ : Fin n → F}
    (hind : ∀ a b : F, a • p₁ + b • p₂ = 0 → a = 0 ∧ b = 0)
    (h₂ : ∃ μ : F, (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (p₂ i)) = μ • p₂)
    (h₁ : ∀ c : F, ∃ μ : F,
      (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ ((p₁ + c • p₂) i)) = μ • (p₁ + c • p₂)) :
    φ = RingEquiv.refl F := by
  classical
  let Am : Matrix (Fin n) (Fin n) F := (A : Matrix (Fin n) (Fin n) F)
  obtain ⟨μ₂, hμ₂⟩ := h₂
  let μ : F → F := fun c => Classical.choose (h₁ c)
  have hμ : ∀ c, Am *ᵥ (fun i => φ ((p₁ + c • p₂) i)) = μ c • (p₁ + c • p₂) :=
    fun c => Classical.choose_spec (h₁ c)
  have hφ_add : ∀ c, (fun i => φ ((p₁ + c • p₂) i)) =
      (fun i => φ (p₁ i)) + φ c • (fun i => φ (p₂ i)) := by
    intro c
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  have h0 : Am *ᵥ (fun i => φ (p₁ i)) = μ 0 • p₁ := by
    simpa using hμ 0
  have hkey : ∀ c, μ c • p₁ + (μ c * c) • p₂ = μ 0 • p₁ + (φ c * μ₂) • p₂ := by
    intro c
    have h := hμ c
    rw [hφ_add c, Matrix.mulVec_add, Matrix.mulVec_smul, h0, hμ₂, smul_smul] at h
    rw [smul_add, smul_smul] at h
    exact h.symm
  have hp₁ : p₁ ≠ 0 := by
    intro hp
    exact one_ne_zero (hind 1 0 (by simpa [hp])).1
  have hp₂ : p₂ ≠ 0 := by
    intro hp
    exact one_ne_zero (hind 0 1 (by simpa [hp])).2
  have hμ0 : μ 0 ≠ 0 := by
    intro h
    have hzero : Am *ᵥ (fun i => φ (p₁ i)) = 0 := by rw [h0, h, zero_smul]
    have hinj : Function.Injective (fun x : Fin n → F => Am *ᵥ x) :=
      Matrix.mulVec_injective_of_isUnit A.isUnit
    have hφp₁ : (fun i => φ (p₁ i)) = 0 := by
      apply hinj
      show Am *ᵥ (fun i => φ (p₁ i)) = Am *ᵥ 0
      rw [hzero, Matrix.mulVec_zero]
    have hp : p₁ = 0 := by
      funext i
      exact φ.injective (by simpa using congrFun hφp₁ i)
    exact hp₁ hp
  have hμeq : ∀ c, μ c = μ 0 := by
    intro c
    have hzero : (μ c - μ 0) • p₁ + (μ c * c - φ c * μ₂) • p₂ = 0 := by
      rw [sub_smul, sub_smul,
        show (μ c • p₁ - μ 0 • p₁) + ((μ c * c) • p₂ - (φ c * μ₂) • p₂) =
          (μ c • p₁ + (μ c * c) • p₂) - (μ 0 • p₁ + (φ c * μ₂) • p₂) by abel]
      rw [hkey c, sub_self]
    exact sub_eq_zero.mp (hind _ _ hzero).1
  have hμ₂eq : μ₂ = μ 0 := by
    have h := hkey 1
    rw [hμeq 1, map_one, mul_one, one_mul] at h
    have hc : μ 0 • p₂ = μ₂ • p₂ := add_left_cancel h
    have hsub : (μ 0 - μ₂) • p₂ = 0 := by rw [sub_smul, hc, sub_self]
    have hcoef : μ 0 - μ₂ = 0 := by
      rcases smul_eq_zero.mp hsub with h' | h'
      · exact h'
      · exact absurd h' hp₂
    exact (sub_eq_zero.mp hcoef).symm
  have hφc : ∀ c, φ c = c := by
    intro c
    have h := hkey c
    rw [hμeq c, hμ₂eq] at h
    have hc : (μ 0 * c) • p₂ = (φ c * μ 0) • p₂ := add_left_cancel h
    have hsub : (μ 0 * c - φ c * μ 0) • p₂ = 0 := by rw [sub_smul, hc, sub_self]
    have hcoef : μ 0 * c - φ c * μ 0 = 0 := by
      rcases smul_eq_zero.mp hsub with h' | h'
      · exact h'
      · exact absurd h' hp₂
    have hmul : μ 0 * c = μ 0 * φ c := by
      rw [mul_comm (φ c) (μ 0)] at hcoef
      exact sub_eq_zero.mp hcoef
    exact (mul_left_cancel₀ hμ0 hmul).symm
  ext c
  exact hφc c

end CFSG.LinearAlgebra
