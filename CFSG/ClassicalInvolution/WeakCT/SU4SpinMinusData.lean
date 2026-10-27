module

public import CFSG.LieType.Universal.Spin.Twisted.Short

public section

namespace CFSG.ClassicalInvolution.WeakCT.SU4

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

section Skew

variable {K : Type} [Field K]

@[expose] def skew6 (a a' g g' ζ ζ' : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, a, g, ζ; -a, 0, ζ', g'; -g, -ζ', 0, a'; -ζ, -g', -a', 0]

@[expose] def pf6 (a a' g g' ζ ζ' : K) : K := a * a' - g * g' + ζ * ζ'

theorem skew6_mul_skew6 (a a' g g' ζ ζ' : K) :
    skew6 a a' g g' ζ ζ' * skew6 (-a') (-a) g' g (-ζ') (-ζ) =
      pf6 a a' g g' ζ ζ' • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew6, pf6, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem skew6_mul_skew6' (a a' g g' ζ ζ' : K) :
    skew6 (-a') (-a) g' g (-ζ') (-ζ) * skew6 a a' g g' ζ ζ' =
      pf6 a a' g g' ζ ζ' • (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew6, pf6, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end Skew

structure KleinData (F K : Type) [Field F] [Field K] [Algebra F K] (σ₀ : K ≃+* K) (b c : F) where
  ω : K
  σσ : ∀ x, σ₀ (σ₀ x) = x
  σ_alg : ∀ r : F, σ₀ (algebraMap F K r) = algebraMap F K r
  ω_sq : ω ^ 2 + algebraMap F K b * ω + algebraMap F K c = 0
  σ_ω : σ₀ ω = -algebraMap F K b - ω
  span : ∀ x : K, ∃ u v : F, x = algebraMap F K u - algebraMap F K v * ω
  two_ne : (2 : K) ≠ 0
  disc_ne : b ^ 2 - 4 * c ≠ 0

namespace KleinData

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  (D : KleinData F K σ₀ b c)

@[expose] def δ : K := 2 * D.ω + algebraMap F K b

theorem σ_δ : σ₀ D.δ = -D.δ := by
  unfold δ
  rw [map_add, map_mul, D.σ_alg, D.σ_ω, map_ofNat]
  ring

theorem δ_mul_δ : D.δ * D.δ = algebraMap F K (b ^ 2 - 4 * c) := by
  have h := D.ω_sq
  unfold δ
  simp only [map_sub, map_pow, map_mul, map_ofNat]
  linear_combination 4 * h

@[expose] def ε : K := D.δ * algebraMap F K (b ^ 2 - 4 * c)⁻¹

theorem δ_mul_ε : D.δ * D.ε = 1 := by
  unfold ε
  rw [← mul_assoc, D.δ_mul_δ, ← map_mul, mul_inv_cancel₀ D.disc_ne, map_one]

theorem σ_ε : σ₀ D.ε = -D.ε := by
  unfold ε
  rw [map_mul, D.σ_δ, D.σ_alg]
  ring

theorem σ_sub_mul (x w : F) :
    σ₀ (algebraMap F K x - algebraMap F K w * D.ω) =
      algebraMap F K x + algebraMap F K w * algebraMap F K b + algebraMap F K w * D.ω := by
  rw [map_sub, map_mul, D.σ_alg, D.σ_alg, D.σ_ω]
  ring

theorem σ_add_mul (x w : F) :
    σ₀ (algebraMap F K x + algebraMap F K w * algebraMap F K b + algebraMap F K w * D.ω) =
      algebraMap F K x - algebraMap F K w * D.ω := by
  rw [map_add, map_add, map_mul, map_mul, D.σ_alg, D.σ_alg, D.σ_alg, D.σ_ω]
  ring

@[expose] def Hs (_D : KleinData F K σ₀ b c) (X : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => σ₀ (X (Fin.rev i) (Fin.rev j))

theorem Hs_skew6 (a a' g g' ζ ζ' : K) :
    D.Hs (skew6 a a' g g' ζ ζ') =
      skew6 (-σ₀ a') (-σ₀ a) (-σ₀ g') (-σ₀ g) (-σ₀ ζ) (-σ₀ ζ') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hs, skew6]

theorem Hs_add (X Y : Matrix (Fin 4) (Fin 4) K) : D.Hs (X + Y) = D.Hs X + D.Hs Y := by
  ext i j
  simp [Hs]

theorem Hs_smul (r : F) (X : Matrix (Fin 4) (Fin 4) K) :
    D.Hs (r • X) = r • D.Hs X := by
  ext i j
  simp [Hs, Algebra.smul_def, D.σ_alg]

theorem Hs_mulVec (X : Matrix (Fin 4) (Fin 4) K) (y : Fin 4 → K) (i : Fin 4) :
    σ₀ ((X *ᵥ y) (Fin.rev i)) = (D.Hs X *ᵥ fun j => σ₀ (y (Fin.rev j))) i := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Hs, Matrix.of_apply]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp)

end KleinData

end CFSG.ClassicalInvolution.WeakCT.SU4
