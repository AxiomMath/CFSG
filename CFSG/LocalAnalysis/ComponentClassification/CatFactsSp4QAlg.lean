module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Kron

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix

variable {K : Type} [Field K]

@[expose] def sA (a : K) : Matrix (Fin 2) (Fin 2) K := !![0, a; 1, 0]

theorem sA_mul_sA (a : K) : sA a * sA a = a • (1 : Matrix (Fin 2) (Fin 2) K) + (0 : K) • sA a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA]

@[expose] def qEmb (a : K) : QuadraticAlgebra K a 0 →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  QuadraticAlgebra.lift ⟨sA a, sA_mul_sA a⟩

theorem qEmb_apply (a : K) (z : QuadraticAlgebra K a 0) :
    qEmb a z = z.re • (1 : Matrix (Fin 2) (Fin 2) K) + z.im • sA a :=
  rfl

theorem qEmb_eq (a : K) (z : QuadraticAlgebra K a 0) :
    qEmb a z = !![z.re, a * z.im; z.im, z.re] := by
  rw [qEmb_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, mul_comm]

theorem qEmb_injective (a : K) : Function.Injective (qEmb a) := by
  intro z w h
  rw [qEmb_eq, qEmb_eq] at h
  have h1 := congrFun (congrFun h 0) 0
  have h2 := congrFun (congrFun h 1) 0
  simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    cons_val_one] at h1 h2
  exact QuadraticAlgebra.ext h1 h2

@[expose] def dA (a : K) : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -a]

theorem qEmb_transpose_mul (a : K) (z : QuadraticAlgebra K a 0) :
    (qEmb a z)ᵀ * dA a = dA a * qEmb a (star z) := by
  rw [qEmb_eq, qEmb_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dA, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem qEmb_algebraMap (a c : K) :
    qEmb a (algebraMap K (QuadraticAlgebra K a 0) c) = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

theorem qEmb_of_commute (a : K) {x : Matrix (Fin 2) (Fin 2) K} (hx : x * sA a = sA a * x) :
    qEmb a (⟨x 0 0, x 1 0⟩ : QuadraticAlgebra K a 0) = x := by
  have e : ∀ i j, (x * sA a) i j = (sA a * x) i j := fun i j => by rw [hx]
  have e00 := e 0 0
  have e10 := e 1 0
  simp [sA, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  rw [qEmb_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination e00 | linear_combination -e00 | linear_combination e10
    | linear_combination -e10

@[expose] def qBlock (a : K) (Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (qEmb a (Z 0 0)) (qEmb a (Z 0 1)) (qEmb a (Z 1 0)) (qEmb a (Z 1 1))

theorem qBlock_mul (a : K) (Z W : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0)) :
    qBlock a (Z * W) = qBlock a Z * qBlock a W := by
  simp only [qBlock, fromBlocks_multiply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]

theorem qBlock_one (a : K) :
    qBlock a (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0)) = 1 := by
  rw [← fromBlocks_one]
  simp [qBlock]

theorem qBlock_injective (a : K) : Function.Injective (qBlock a) := by
  intro Z W h
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp h
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact qEmb_injective a h1
  · exact qEmb_injective a h2
  · exact qEmb_injective a h3
  · exact qEmb_injective a h4

theorem qBlock_map (a : K) (g : Matrix (Fin 2) (Fin 2) K) :
    qBlock a (g.map (algebraMap K (QuadraticAlgebra K a 0))) = kron g 1 := by
  simp only [qBlock, kron, map_apply, qEmb_algebraMap]

theorem exists_qBlock_of_commute (a : K) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hX : X * kron 1 (sA a) = kron 1 (sA a) * X) : ∃ Z, qBlock a Z = X := by
  have hT : kron 1 (sA a) = fromBlocks (sA a) 0 0 (sA a) := by
    simp [kron]
  rw [hT, ← fromBlocks_toBlocks X, fromBlocks_multiply, fromBlocks_multiply] at hX
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp hX
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h1 h2 h3 h4
  refine ⟨!![⟨X.toBlocks₁₁ 0 0, X.toBlocks₁₁ 1 0⟩, ⟨X.toBlocks₁₂ 0 0, X.toBlocks₁₂ 1 0⟩;
    ⟨X.toBlocks₂₁ 0 0, X.toBlocks₂₁ 1 0⟩, ⟨X.toBlocks₂₂ 0 0, X.toBlocks₂₂ 1 0⟩], ?_⟩
  conv_rhs => rw [← fromBlocks_toBlocks X]
  simp only [qBlock, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  rw [qEmb_of_commute a h1, qEmb_of_commute a h2, qEmb_of_commute a h3, qEmb_of_commute a h4]

theorem qBlock_transpose_mul (a : K) (Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0)) :
    (qBlock a Z)ᵀ * kron 1 (dA a) = kron 1 (dA a) * qBlock a Zᴴ := by
  have hD : kron (1 : Matrix (Fin 2) (Fin 2) K) (dA a) = fromBlocks (dA a) 0 0 (dA a) := by
    simp [kron]
  rw [hD]
  simp only [qBlock, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, conjTranspose_apply, qEmb_transpose_mul]

@[expose] def jE (a : K) : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0) := !![0, 1; -1, 0]

theorem kron_J₁_one_eq_qBlock (a : K) :
    kron J₁ (1 : Matrix (Fin 2) (Fin 2) K) = qBlock a (jE a) := by
  simp [kron, qBlock, jE, J₁, map_neg, map_one, map_zero]

@[expose] def dAinv (a : K) : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -a⁻¹]

theorem dA_mul_dAinv {a : K} (ha : a ≠ 0) : dA a * dAinv a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dA, dAinv, ha]

theorem dAinv_mul_dA {a : K} (ha : a ≠ 0) : dAinv a * dA a = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dA, dAinv, ha]

theorem qBlock_symplectic_iff {a : K} (ha : a ≠ 0)
    (Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0)) :
    (qBlock a Z)ᵀ * kron J₁ (dA a) * qBlock a Z = kron J₁ (dA a) ↔ Zᴴ * jE a * Z = jE a := by
  have hsplit : kron J₁ (dA a) = kron 1 (dA a) * kron J₁ 1 := by
    rw [kron_mul, Matrix.one_mul, Matrix.mul_one]
  have hinv : kron 1 (dAinv a) * kron 1 (dA a) = 1 := by
    rw [kron_mul, Matrix.one_mul, dAinv_mul_dA ha, kron_one_one]
  rw [hsplit, ← Matrix.mul_assoc, qBlock_transpose_mul, kron_J₁_one_eq_qBlock a,
    Matrix.mul_assoc, ← qBlock_mul, Matrix.mul_assoc, ← qBlock_mul]
  constructor
  · intro h
    apply qBlock_injective a
    have := congrArg (fun X => kron 1 (dAinv a) * X) h
    simp only [← Matrix.mul_assoc, hinv, Matrix.one_mul] at this
    rw [Matrix.mul_assoc] at this
    rw [Matrix.mul_assoc]
    exact this
  · intro h
    rw [← Matrix.mul_assoc Zᴴ, h]

theorem exists_map_of_det_eq_one_qAlg {a : K} (h2 : (2 : K) ≠ 0)
    {Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra K a 0)}
    (hsym : Zᴴ * jE a * Z = jE a) (hdet : Z.det = 1) :
    ∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧
      Z = g.map (algebraMap K (QuadraticAlgebra K a 0)) := by
  have hT : Zᵀ * jE a * Z = jE a := by
    rw [jE, transpose_mul_J₁_mul, hdet, one_smul]
  have hu : IsUnit (jE a * Z) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_mul, hdet, mul_one]
    simp [jE, det_fin_two]
  have hHT : Zᴴ = Zᵀ := by
    apply hu.mul_right_cancel
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hsym, hT]
  have hstar : ∀ i j, star (Z i j) = Z i j := fun i j => by
    have := congrFun (congrFun hHT j) i
    simpa using this
  have him : ∀ i j, (Z i j).im = 0 := fun i j => by
    have h := congrArg QuadraticAlgebra.im (hstar i j)
    rw [QuadraticAlgebra.im_star] at h
    have h' : (2 : K) * (Z i j).im = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2
  refine ⟨Matrix.of fun i j => (Z i j).re, ?_, ?_⟩
  · have hZ : Z = (Matrix.of fun i j => (Z i j).re).map
        (algebraMap K (QuadraticAlgebra K a 0)) := by
      ext i j
      · simp
      · simp [him i j]
    have h1 : algebraMap K (QuadraticAlgebra K a 0) (Matrix.of fun i j => (Z i j).re).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hZ, hdet]
    exact (algebraMap K (QuadraticAlgebra K a 0)).injective (by rw [h1, map_one])
  · ext i j
    · simp
    · simp [him i j]

end CFSG.ComponentClassification.CatFactsSp4
