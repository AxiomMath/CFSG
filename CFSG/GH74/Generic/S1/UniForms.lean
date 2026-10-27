module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import Mathlib.Data.Matrix.ColumnRowPartitioned

public section

namespace CFSG.GH74.Generic.S1.Uni

open Matrix

variable {K : Type} [Field K]

theorem exists_alt_conj (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 4) (Fin 4) K} (hA : Aᵀ = -A)
    (hdet : A.det ≠ 0) :
    ∃ N : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K, Nᵀ * A * N = Matrix.fromBlocks 0 (-1) 1 0 := by
  classical
  have hBalt : (toBilin' A).IsAlt := fun v => by
    rw [Matrix.toBilin'_apply']
    have hx : v ⬝ᵥ (A *ᵥ v) = -(v ⬝ᵥ (A *ᵥ v)) := by
      conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hA, neg_mulVec, neg_dotProduct,
        dotProduct_comm]
    have h3 : (2 : K) * (v ⬝ᵥ (A *ᵥ v)) = 0 := by linear_combination hx
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hBnd : (toBilin' A).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 hdet
  obtain ⟨k, b, hb⟩ := hBalt.exists_basis_toMatrix_eq_J hBnd
  have hk : 4 = k + k := by
    have h := Module.finrank_eq_card_basis b
    rwa [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h
  obtain rfl : k = 2 := by omega
  refine ⟨(Pi.basisFun K (Fin 4)).toMatrix b, ?_⟩
  have h1 := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin 4)) b (toBilin' A)
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin', hb] at h1
  exact h1


theorem hyp_of_diag [Finite K] (hodd : Odd (Nat.card K)) {a b c e : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (he : e ≠ 0) {s : K} (hs : s * s = a * b * c * e) :
    ∃ N : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K,
      Nᵀ * Matrix.diagonal ![a, b, c, e] * N = Matrix.fromBlocks 0 1 1 0 := by
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨z, t, hzt⟩ := CFSG.ComponentClassification.CatalogueBOddQuadratic.exists_weighted_ternary_zero
    hodd hc he a
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) he hs.symm
  obtain ⟨κ, hκ2⟩ : ∃ κ : K, κ ^ 2 * a * c * e = b := by
    refine ⟨b / s, ?_⟩
    field_simp
    rw [sq, hs]
    ring
  set m1 : K := κ * e * t with hm1
  set m2 : K := -(κ * c * z) with hm2
  let E : Matrix (Fin 4) (Fin 2) K := !![1, 0; 0, 1; z, m1; t, m2]
  let Fm : Matrix (Fin 4) (Fin 2) K :=
    !![1 / (2 * a), 0; 0, 1 / (2 * b); -z / (2 * a), -m1 / (2 * b); -t / (2 * a), -m2 / (2 * b)]
  let D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![a, b, c, e]
  have hEE : Eᵀ * D * E = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, D, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply, Matrix.transpose_apply]
    · linear_combination hzt
    · rw [hm1, hm2]; ring
    · rw [hm1, hm2]; ring
    · rw [hm1, hm2]; linear_combination (κ ^ 2 * c * e) * hzt - hκ2
  have hEF : Eᵀ * D * Fm = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [E, D, Fm, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
        Matrix.transpose_apply]
    · field_simp
      linear_combination (-1 : K) * hzt
    · rw [hm1, hm2]; field_simp; ring
    · rw [hm1, hm2]; field_simp; ring
    · rw [hm1, hm2]; field_simp; linear_combination (-(κ ^ 2 * c * e)) * hzt + hκ2
  have hFE : Fmᵀ * D * E = 1 := by
    have := congrArg Matrix.transpose hEF
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_one, Matrix.transpose_transpose,
      Matrix.diagonal_transpose] at this
    rw [← this]
    simp only [D, Matrix.mul_assoc]
  have hFF : Fmᵀ * D * Fm = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Fm, D, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
        Matrix.transpose_apply]
    · field_simp
      linear_combination hzt
    · rw [hm1, hm2]; field_simp; ring
    · rw [hm1, hm2]; field_simp; ring
    · rw [hm1, hm2]; field_simp; linear_combination (κ ^ 2 * c * e) * hzt - hκ2
  refine ⟨Matrix.fromCols E Fm, ?_⟩
  rw [Matrix.transpose_fromCols, Matrix.mul_assoc, Matrix.mul_fromCols,
    Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hEE, hEF, hFE, hFF]


theorem exists_hyp_conj [Finite K] (hodd : Odd (Nat.card K)) {S : Matrix (Fin 4) (Fin 4) K}
    (hS : Sᵀ = S) (hdet : S.det ≠ 0) (hsq : IsSquare S.det) :
    ∃ N : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K, Nᵀ * S * N = Matrix.fromBlocks 0 1 1 0 := by
  classical
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hBsymm : (toBilin' S).IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm).2 hS
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := toBilin' S)
    (LinearMap.IsSymm.mk fun x y => hBsymm.eq x y)
  let v' : Module.Basis (Fin 4) K (Fin 4 → K) := v.reindex (finCongr (Module.finrank_fin_fun K))
  have hv' : ∀ i j, i ≠ j → (toBilin' S) (v' i) (v' j) = 0 := by
    intro i j hij
    have := hv (show (finCongr (Module.finrank_fin_fun K)).symm i ≠
      (finCongr (Module.finrank_fin_fun K)).symm j from fun h => hij (by simpa using h))
    simpa [v', Module.Basis.reindex_apply] using this
  set N₁ : Matrix (Fin 4) (Fin 4) K := (Pi.basisFun K (Fin 4)).toMatrix v' with hN₁
  have hD : N₁ᵀ * S * N₁ = Matrix.diagonal fun i => (toBilin' S) (v' i) (v' i) := by
    have h1 := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K (Fin 4)) v' (toBilin' S)
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h1
    rw [h1]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [hv' i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdetN₁ : N₁.det ≠ 0 := by
    have := (Pi.basisFun K (Fin 4)).isUnit_det v'
    rw [Module.Basis.det_apply] at this
    exact this.ne_zero
  set d : Fin 4 → K := fun i => (toBilin' S) (v' i) (v' i) with hd
  have hdetD : (Matrix.diagonal d).det = N₁.det * S.det * N₁.det := by
    rw [← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [Matrix.det_diagonal, Fin.prod_univ_four] at hdetD
  obtain ⟨r, hr⟩ := hsq
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    have : d 0 * d 1 * d 2 * d 3 = 0 := by
      fin_cases i <;> simp_all
    rw [hdetD] at this
    exact mul_ne_zero (mul_ne_zero hdetN₁ hdet) hdetN₁ this
  have hdeq : d = ![d 0, d 1, d 2, d 3] := by
    funext i; fin_cases i <;> rfl
  obtain ⟨N₂, hN₂⟩ := hyp_of_diag hodd (hd0 0) (hd0 1) (hd0 2) (hd0 3)
    (s := N₁.det * r) (by rw [hdetD, hr]; ring)
  refine ⟨N₁ * N₂, ?_⟩
  rw [Matrix.transpose_mul]
  have : (N₂ᵀ * N₁ᵀ) * S * (N₁ * N₂) = N₂ᵀ * (N₁ᵀ * S * N₁) * N₂ := by simp only [Matrix.mul_assoc]
  rw [this, hD, hdeq]
  exact hN₂

end CFSG.GH74.Generic.S1.Uni
