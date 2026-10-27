module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open Matrix CFSG.GH74.GLS.IVK.Proofs2

namespace MF163

variable {K : Type} [Field K]

@[expose] def jMat (μ : K) : Matrix (Fin 2) (Fin 2) K := !![0, -μ; μ, 0]

theorem jMat_mul_jMat_inv (μ : Kˣ) : jMat (μ : K) * jMat (-(μ⁻¹ : Kˣ) : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem jMat_inv_mul_jMat (μ : Kˣ) : jMat (-(μ⁻¹ : Kˣ) : K) * jMat (μ : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem jMat_inv_transpose (μ : Kˣ) (A : GL (Fin 2) K) :
    jMat (μ : K) * ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ * jMat (-(μ⁻¹ : Kˣ) : K) =
      (A : Matrix (Fin 2) (Fin 2) K) * ((A : Matrix (Fin 2) (Fin 2) K).det⁻¹ •
        (1 : Matrix (Fin 2) (Fin 2) K)) := by
  rw [Matrix.coe_units_inv]
  have hA : (A : Matrix (Fin 2) (Fin 2) K) = !![(A : Matrix (Fin 2) (Fin 2) K) 0 0,
      (A : Matrix (Fin 2) (Fin 2) K) 0 1; (A : Matrix (Fin 2) (Fin 2) K) 1 0,
      (A : Matrix (Fin 2) (Fin 2) K) 1 1] := Matrix.eta_fin_two _
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := Lemma41aL3.det_ne_zero_gl A
  rw [hA] at hdet ⊢
  set a := (A : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) K) 1 1
  rw [Matrix.det_fin_two_of] at hdet
  have hμ : (μ : K) ≠ 0 := μ.ne_zero
  rw [Matrix.inv_def, Matrix.adjugate_fin_two_of, Matrix.det_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply] <;>
    simp [jMat] <;> field_simp

theorem blkMat_transpose (X : Matrix (Fin 2) (Fin 2) K) (d : K) :
    (Lemma41aL3.blkMat X d)ᵀ = Lemma41aL3.blkMat Xᵀ d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat]

theorem trace_eq_of_conj {n : ℕ} {g : GL (Fin n) K} {x y : Matrix (Fin n) (Fin n) K} {ω : K}
    (h : (g : Matrix (Fin n) (Fin n) K) * x * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ω • y) :
    trace x = ω * trace y ∧ trace (x * x) = ω ^ 2 * trace (y * y) := by
  have h1 := trace_units_conj g x
  have h2 := trace_units_conj g (x * x)
  have hsq : (g : Matrix (Fin n) (Fin n) K) * (x * x) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (ω • y) * (ω • y) := by
    rw [← h]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [h] at h1
  rw [hsq, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h2
  refine ⟨by rw [← h1, trace_smul, smul_eq_mul], ?_⟩
  rw [← h2, trace_smul, smul_eq_mul, sq]

theorem block_of_commute_diag {g : Matrix (Fin 3) (Fin 3) K} {l k : K} (hlk : l ≠ k)
    (h : g * diagonal ![l, l, k] = diagonal ![l, l, k] * g) :
    g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  simp only [mul_diagonal, diagonal_mul] at e
  have hkl : k - l ≠ 0 := sub_ne_zero.2 hlk.symm
  have e02 := e 0 2
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  simp at e02 e12 e20 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : g 0 2 * (k - l) = 0 := by linear_combination e02
    exact (mul_eq_zero.1 this).resolve_right hkl
  · have : g 1 2 * (k - l) = 0 := by linear_combination e12
    exact (mul_eq_zero.1 this).resolve_right hkl
  · have : g 2 0 * (k - l) = 0 := by linear_combination -e20
    exact (mul_eq_zero.1 this).resolve_right hkl
  · have : g 2 1 * (k - l) = 0 := by linear_combination -e21
    exact (mul_eq_zero.1 this).resolve_right hkl

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
