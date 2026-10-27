module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronFix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCentFix

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.Burgoyne.PSL (signMat signMat_mul_self reflGL rotGL rotMat
  transpose_rotMat rotMat_mul rotMat_one_zero rotMat_apply_ne_zero commutatorElement_reflGL_rotGL
  rotMat_neg_one_zero)
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

variable (K) in
@[expose] def permGL (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) K :=
  (Matrix.permMatrixHom (n := Fin n) (R := K)).toHomUnits

theorem coe_permGL (σ : Equiv.Perm (Fin n)) :
    ((permGL K n σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = σ⁻¹.permMatrix K := rfl

theorem permGL_orth (σ : Equiv.Perm (Fin n)) :
    ((permGL K n σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      ((permGL K n σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [coe_permGL, transpose_permMatrix, inv_inv, ← permMatrix_mul, inv_mul_cancel,
    permMatrix_one]

theorem reflGL_orth (i : Fin n) :
    ((reflGL (K := K) i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      ((reflGL (K := K) i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  change (signMat K {i})ᵀ * signMat K {i} = 1
  rw [signMat, diagonal_transpose, ← signMat, signMat_mul_self]

theorem rotGL_orth {i j : Fin n} (hij : i ≠ j) {a b : K} (hab : a ^ 2 + b ^ 2 = 1) :
    ((rotGL i j hij hab : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      ((rotGL i j hij hab : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  change (rotMat i j a b)ᵀ * rotMat i j a b = 1
  rw [transpose_rotMat, rotMat_mul hij, show a * a - -b * b = 1 by linear_combination hab,
    show a * b + -b * a = 0 by ring, rotMat_one_zero]

theorem signMat_pair_eq_commutator {i j : Fin n} (hij : i ≠ j)
    (h01 : (0 : K) ^ 2 + (1 : K) ^ 2 = 1) :
    ((⁅reflGL (K := K) i, rotGL i j hij h01⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      signMat K {i, j} := by
  rw [commutatorElement_reflGL_rotGL,
    show (0 : K) ^ 2 - 1 ^ 2 = -1 by ring, show -(2 * (0 : K) * 1) = 0 by ring,
    rotMat_neg_one_zero hij]

theorem coe_commutator_permGL (σ τ : Equiv.Perm (Fin n)) :
    ((⁅permGL K n σ, permGL K n τ⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (⁅σ, τ⁆)⁻¹.permMatrix K := by
  rw [← map_commutatorElement, coe_permGL]

theorem kronGL_mem_isoCent_blkDiag {W₀ j : Matrix (Fin 2) (Fin 2) K} {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n W₀)
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n j) {X : GL (Fin n) K}
    (hX : (X : Matrix (Fin n) (Fin n) K)ᵀ * X = 1) : kronGL K n X ∈ isoCent R A := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CatalogueBGraphForm.mem_isometryGroup]
    change (kronI K n (X : Matrix (Fin n) (Fin n) K))ᵀ * R.val *
      kronI K n (X : Matrix (Fin n) (Fin n) K) = R.val
    rw [show R.val = (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) from rfl, hR,
      resMat_transpose_mul (algebraMap K (Matrix (Fin 2) (Fin 2) K)) (RingHom.id K)
        (fun x => by rw [RingHom.id_apply, Algebra.algebraMap_eq_smul_one, transpose_smul,
          transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]),
      Matrix.mul_assoc, ← map_mul]
    have : ((X : Matrix (Fin n) (Fin n) K).map (RingHom.id K))ᵀ * X = 1 := by
      have hm : (X : Matrix (Fin n) (Fin n) K).map (RingHom.id K) = X := by
        ext
        rfl
      rw [hm]
      exact hX
    rw [this, map_one, Matrix.mul_one]
  · rw [mem_centralizer_singleton_iff]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hA, coe_kronGL, resMat_eq, blkDiag, ← map_mul, ← map_mul]
    congr 1
    ext i k : 1
    rw [mul_diagonal, diagonal_mul]
    simp only [map_apply]
    exact Algebra.commutes _ _

theorem map_mul_diagonal_comm {Λ : Type*} [CommRing Λ] [Algebra K Λ]
    {X : Matrix (Fin n) (Fin n) K} {g : Fin n → Λ} (hX : ∀ x y, X x y ≠ 0 → g x = g y) :
    X.map (algebraMap K Λ) * diagonal g = diagonal g * X.map (algebraMap K Λ) := by
  ext x y
  rw [mul_diagonal, diagonal_mul, map_apply]
  by_cases h : X x y = 0
  · rw [h, map_zero, zero_mul, mul_zero]
  · rw [hX x y h, mul_comm]

theorem reflGL_support (i : Fin n) {x y : Fin n}
    (h : ((reflGL (K := K) i : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y ≠ 0) : x = y := by
  by_contra hxy
  apply h
  change signMat K {i} x y = 0
  rw [signMat, diagonal_apply_ne _ hxy]

theorem permGL_swap_support {i j : Fin n} {x y : Fin n}
    (h : ((permGL K n (Equiv.swap i j) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y ≠ 0) :
    y = Equiv.swap i j x := by
  rw [coe_permGL, Equiv.swap_inv, permMatrix_apply'] at h
  split_ifs at h with hc
  · exact hc.symm
  · exact absurd rfl h

end CFSG.ComponentClassification.Burgoyne.O
