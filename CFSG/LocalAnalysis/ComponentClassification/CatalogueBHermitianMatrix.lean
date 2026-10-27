module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianBasis

public section

namespace CFSG.ComponentClassification.CatalogueBHermitian

noncomputable section

universe u

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type u} [Field K] (sigma : K ≃+* K) {n : ℕ}

@[expose] def matrixForm (A : Matrix (Fin n) (Fin n) K) :
    (Fin n → K) →ₛₗ[sigma.toRingHom] (Fin n → K) →ₗ[K] K where
  toFun x := (hermL sigma x).comp A.mulVecLin
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change herm sigma (x + y) (A *ᵥ z) =
      herm sigma x (A *ᵥ z) + herm sigma y (A *ᵥ z)
    exact herm_add_left sigma x y (A *ᵥ z)
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    change herm sigma (c • x) (A *ᵥ z) = sigma c * herm sigma x (A *ᵥ z)
    exact herm_smul_left sigma c x (A *ᵥ z)

theorem matrixForm_apply (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    matrixForm sigma A x y = herm sigma x (A *ᵥ y) := rfl

theorem herm_matrix_adjoint (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    herm sigma (A *ᵥ x) y = herm sigma x (conjTr sigma A *ᵥ y) := by
  have hm : (fun i => sigma ((A *ᵥ x) i)) = A.map sigma *ᵥ fun i => sigma (x i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  change (fun i => sigma ((A *ᵥ x) i)) ⬝ᵥ y =
    (fun i => sigma (x i)) ⬝ᵥ (conjTr sigma A *ᵥ y)
  rw [hm, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, conjTr, mulVec_transpose]

theorem matrixForm_isSymm (hsigma : sigma ^ 2 = 1)
    (A : Matrix (Fin n) (Fin n) K) (hA : conjTr sigma A = A) :
    (matrixForm sigma A).IsSymm where
  eq x y := by
    change sigma (herm sigma x (A *ᵥ y)) = herm sigma y (A *ᵥ x)
    rw [← herm_conj sigma (CatalogueBUnitaryNorm.involutive sigma hsigma),
      herm_matrix_adjoint, hA]

theorem matrixForm_nondegenerate (A : GL (Fin n) K) :
    (matrixForm sigma (A : Matrix (Fin n) (Fin n) K)).Nondegenerate := by
  constructor
  · intro x hx
    apply eq_zero_of_herm sigma
    intro z
    have hz := hx ((A⁻¹ : GL (Fin n) K).val *ᵥ z)
    rw [matrixForm_apply, mulVec_mulVec, A.mul_inv, one_mulVec] at hz
    exact hz
  · intro y hy
    have hz : (A : Matrix (Fin n) (Fin n) K) *ᵥ y = 0 := by
      funext i
      have hi := hy (Pi.single i 1)
      simpa only [matrixForm_apply, herm_single_left, map_one, one_mul, Pi.zero_apply] using hi
    calc
      y = (A⁻¹ : GL (Fin n) K).val *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) := by
        rw [mulVec_mulVec, A.inv_mul, one_mulVec]
      _ = 0 := by rw [hz, mulVec_zero]

theorem matrixForm_mulVec (A B : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    matrixForm sigma A (B *ᵥ x) (B *ᵥ y) =
      herm sigma x ((conjTr sigma B * A * B) *ᵥ y) := by
  simp only [matrixForm_apply, herm_matrix_adjoint, mulVec_mulVec, Matrix.mul_assoc]

theorem conjugateTranspose_involutive (hsigma : sigma ^ 2 = 1)
    (A : Matrix (Fin n) (Fin n) K) : conjTr sigma (conjTr sigma A) = A := by
  ext i j
  exact CatalogueBUnitaryNorm.involutive sigma hsigma (A i j)

@[expose] def conjugateTransposeGL (B : GL (Fin n) K) : GL (Fin n) K where
  val := conjTr sigma (B : Matrix (Fin n) (Fin n) K)
  inv := conjTr sigma (B⁻¹ : GL (Fin n) K).val
  val_inv := by rw [← conjTr_mul, B.inv_mul, conjTr_one]
  inv_val := by rw [← conjTr_mul, B.mul_inv, conjTr_one]

theorem conjugateTransposeGL_val (B : GL (Fin n) K) :
    (conjugateTransposeGL sigma B).val = conjTr sigma B.val := rfl

theorem exists_orthonormal_matrix [Finite K] (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (A : GL (Fin n) K) (hA : conjTr sigma A.val = A.val) :
    ∃ B : GL (Fin n) K, conjTr sigma B.val * A.val * B.val = 1 := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin n) K (Fin n → K),
      ∀ i j, matrixForm sigma A.val (b i) (b j) = if i = j then 1 else 0 := by
    have hb := exists_orthonormal_basis (matrixForm sigma A.val)
      (matrixForm_isSymm sigma hsigma A.val hA) (matrixForm_nondegenerate sigma A)
      hsigma hne
    rw [Module.finrank_fin_fun K] at hb
    exact hb
  let b0 := Pi.basisFun K (Fin n)
  let B : GL (Fin n) K :=
    { val := b0.toMatrix b
      inv := b.toMatrix b0
      val_inv := b0.toMatrix_mul_toMatrix_flip b
      inv_val := b.toMatrix_mul_toMatrix_flip b0 }
  have hcol (i : Fin n) : B.val *ᵥ Pi.single i 1 = b i := by
    ext j
    simp [B, b0, Module.Basis.toMatrix_apply]
  refine ⟨B, ?_⟩
  ext i j
  have hij := hb i j
  rw [← hcol i, ← hcol j, matrixForm_mulVec, herm_single_left,
    map_one, one_mul, mulVec_single_one] at hij
  simpa only [Matrix.col_apply, Matrix.one_apply] using hij

theorem exists_hermitian_factorization [Finite K]
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (A : GL (Fin n) K) (hA : conjTr sigma A.val = A.val) :
    ∃ H : GL (Fin n) K, A.val = H.val * conjTr sigma H.val := by
  obtain ⟨B, hB⟩ := exists_orthonormal_matrix sigma hsigma hne A hA
  let H := conjugateTransposeGL sigma B⁻¹
  refine ⟨H, ?_⟩
  change A.val = conjTr sigma (B⁻¹ : GL (Fin n) K).val *
    conjTr sigma (conjTr sigma (B⁻¹ : GL (Fin n) K).val)
  rw [conjugateTranspose_involutive sigma hsigma]
  have hleft : conjTr sigma (B⁻¹ : GL (Fin n) K).val * conjTr sigma B.val = 1 := by
    rw [← conjTr_mul, B.mul_inv, conjTr_one]
  calc
    A.val = conjTr sigma (B⁻¹ : GL (Fin n) K).val *
        (conjTr sigma B.val * A.val * B.val) * (B⁻¹ : GL (Fin n) K).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hleft,
        Matrix.one_mul, Matrix.mul_assoc, B.mul_inv, Matrix.mul_one]
    _ = conjTr sigma (B⁻¹ : GL (Fin n) K).val * (B⁻¹ : GL (Fin n) K).val := by
      rw [hB, Matrix.mul_one]

theorem exists_hermitian_matrix_factorization [Finite K]
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (A : GL (Fin n) K) (hA : (sigma.toRingHom.mapMatrix A.val).transpose = A.val) :
    ∃ H : GL (Fin n) K, A.val = H.val * (sigma.toRingHom.mapMatrix H.val).transpose :=
  exists_hermitian_factorization sigma hsigma hne A hA

end

end CFSG.ComponentClassification.CatalogueBHermitian
