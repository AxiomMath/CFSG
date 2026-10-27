module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowSFacts
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

namespace Catalog7L4E

open Matrix CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

section Pfaffian

variable {k : Type*} [Field k]

theorem det_four (A : Matrix (Fin 4) (Fin 4) k) : A.det =
    A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 +
        A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
      A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3 +
        A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
      A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3 +
        A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
      A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2 +
        A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, Fin.succAbove, Matrix.submatrix]
  ring

theorem det_eq_pfaffian_sq (h2 : (2 : k) ≠ 0) {M : Matrix (Fin 4) (Fin 4) k} (hM : Mᵀ = -M) :
    M.det = (M 0 1 * M 2 3 - M 0 2 * M 1 3 + M 0 3 * M 1 2) ^ 2 := by
  have hji : ∀ i j, M j i = -M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa using this
  have hii : ∀ i, M i i = 0 := fun i => by
    have h := hji i i
    have : (2 : k) * M i i = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [det_four, hii 0, hii 1, hii 2, hii 3, hji 0 1, hji 0 2, hji 0 3, hji 1 2, hji 1 3,
    hji 2 3]
  ring

end Pfaffian

section Split

variable {k : Type*} [Field k]

@[expose] def flatL (k : Type*) [Field k] : Matrix (Fin 2) (Fin 2) k →ₗ[k] (Fin 4 → k) where
  toFun X := ![X 0 0, X 0 1, X 1 0, X 1 1]
  map_add' X Y := by
    funext i
    fin_cases i <;> simp
  map_smul' c X := by
    funext i
    fin_cases i <;> simp

@[expose] def detGram (k : Type*) [Field k] : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, 0, 1; 0, 0, -1, 0; 0, -1, 0, 0; 1, 0, 0, 0]

theorem detPolar_eq_flat (X Y : Matrix (Fin 2) (Fin 2) k) :
    detPolar X Y = flatL k X ⬝ᵥ (detGram k *ᵥ flatL k Y) := by
  rw [detPolar_eq]
  simp [flatL, detGram, dotProduct, Fin.sum_univ_four, mulVec]
  ring

theorem det_detGram : (detGram k).det = 1 := by
  rw [det_four]
  simp [detGram]

theorem matrix_eq_of_dotProduct {n : Type*} [Fintype n] [DecidableEq n]
    {M N : Matrix n n k} (h : ∀ v w : n → k, v ⬝ᵥ (M *ᵥ w) = v ⬝ᵥ (N *ᵥ w)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

theorem isSquare_det_of_split (h2 : (2 : k) ≠ 0) {A : GL (Fin 4) k}
    (hA : (A : Matrix (Fin 4) (Fin 4) k)ᵀ = A) (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k)
    (hψ : ∀ v, v ⬝ᵥ (((A⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = (ψ v).det) :
    ∃ s : kˣ, GeneralLinearGroup.det A = s ^ 2 := by
  classical
  set Ai : Matrix (Fin 4) (Fin 4) k := ((A⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) with hAi
  have hAiT : Aiᵀ = Ai := by
    have hAAi : (A : Matrix (Fin 4) (Fin 4) k) * Ai = 1 := by
      rw [hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc Aiᵀ = Aiᵀ * ((A : Matrix (Fin 4) (Fin 4) k) * Ai) := by rw [hAAi, Matrix.mul_one]
      _ = ((A : Matrix (Fin 4) (Fin 4) k) * Ai)ᵀ * Ai := by
          rw [transpose_mul, hA, Matrix.mul_assoc]
      _ = Ai := by rw [hAAi, transpose_one, Matrix.one_mul]
  set P := LinearMap.toMatrix' ((flatL k).comp (ψ : (Fin 4 → k) →ₗ[k] _)) with hP
  have hPv : ∀ v, P *ᵥ v = flatL k (ψ v) := fun v => by
    rw [hP, LinearMap.toMatrix'_mulVec]
    rfl
  have hkey : (2 : k) • Ai = Pᵀ * detGram k * P := by
    apply matrix_eq_of_dotProduct
    intro v w
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul,
      two_mul_dotProduct_eq ψ hAiT hψ v w, detPolar_eq_flat, ← hPv, ← hPv]
    conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hdet := congrArg Matrix.det hkey
  rw [det_smul, det_mul, det_mul, det_transpose, det_detGram, Fintype.card_fin, mul_one] at hdet
  have hAi0 : Ai.det ≠ 0 := by
    rw [hAi]
    exact (A⁻¹).isUnit.map (Matrix.detMonoidHom (n := Fin 4) (R := k)) |>.ne_zero
  have hP0 : P.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet
    exact hAi0 ((mul_eq_zero.mp hdet).resolve_left (pow_ne_zero _ h2))
  have hA0 : (A : Matrix (Fin 4) (Fin 4) k).det ≠ 0 :=
    A.isUnit.map (Matrix.detMonoidHom (n := Fin 4) (R := k)) |>.ne_zero
  have hAAi : (A : Matrix (Fin 4) (Fin 4) k).det * Ai.det = 1 := by
    rw [hAi, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  refine ⟨Units.mk0 (4 / P.det) (div_ne_zero h4 hP0), Units.ext ?_⟩
  rw [GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val, Units.val_mk0]
  have e1 : (A : Matrix (Fin 4) (Fin 4) k).det = (Ai.det)⁻¹ := eq_inv_of_mul_eq_one_left hAAi
  rw [e1]
  have e2 : Ai.det * 16 = P.det * P.det := by
    have : (2 : k) ^ 4 = 16 := by norm_num
    rw [this] at hdet
    linear_combination hdet
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 4 * 4 := by norm_num
    rw [this]
    exact mul_ne_zero h4 h4
  rw [div_pow, inv_eq_iff_eq_inv, inv_div]
  field_simp
  linear_combination e2

end Split

section Trace

variable {k : Type} [Field k] (ν : kˣ) (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k))

@[expose] def omegaE (x y : Fin 2 → extension (ν : k)) : extension (ν : k) :=
  x 0 * y 1 - x 1 * y 0

theorem omegaE_swap (x y : Fin 2 → extension (ν : k)) : omegaE ν y x = -omegaE ν x y := by
  simp only [omegaE]
  ring

theorem omegaE_mulVec (g : Matrix (Fin 2) (Fin 2) (extension (ν : k)))
    (x y : Fin 2 → extension (ν : k)) :
    omegaE ν (g *ᵥ x) (g *ᵥ y) = g.det * omegaE ν x y := by
  simp only [omegaE, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

@[expose] def traceForm (θ : extension (ν : k)) : LinearMap.BilinForm k (Fin 4 → k) :=
  LinearMap.mk₂ k (fun v w => Algebra.trace k (extension (ν : k))
      (θ * omegaE ν (Ψ.symm v) (Ψ.symm w)))
    (fun v v' w => by
      rw [← map_add]
      congr 1
      simp only [omegaE, map_add, Pi.add_apply]
      ring)
    (fun c v w => by
      rw [smul_eq_mul, ← smul_eq_mul (a := c), ← map_smul, LinearEquiv.map_smul]
      congr 1
      simp only [omegaE, Pi.smul_apply, Algebra.smul_def]
      ring)
    (fun v w w' => by
      rw [← map_add]
      congr 1
      simp only [omegaE, map_add, Pi.add_apply]
      ring)
    (fun c v w => by
      rw [smul_eq_mul, ← smul_eq_mul (a := c), ← map_smul, LinearEquiv.map_smul]
      congr 1
      simp only [omegaE, Pi.smul_apply, Algebra.smul_def]
      ring)

theorem traceForm_apply (θ : extension (ν : k)) (v w : Fin 4 → k) :
    traceForm ν Ψ θ v w =
      Algebra.trace k (extension (ν : k)) (θ * omegaE ν (Ψ.symm v) (Ψ.symm w)) := rfl

@[expose] def traceGram (θ : extension (ν : k)) : Matrix (Fin 4) (Fin 4) k :=
  LinearMap.BilinForm.toMatrix' (traceForm ν Ψ θ)

theorem dotProduct_traceGram (θ : extension (ν : k)) (v w : Fin 4 → k) :
    v ⬝ᵥ (traceGram ν Ψ θ *ᵥ w) = traceForm ν Ψ θ v w := by
  rw [traceGram, ← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix']

theorem traceGram_transpose (θ : extension (ν : k)) :
    (traceGram ν Ψ θ)ᵀ = -traceGram ν Ψ θ := by
  apply matrix_eq_of_dotProduct
  intro v w
  rw [neg_mulVec, dotProduct_neg, dotProduct_mulVec, vecMul_transpose, dotProduct_comm,
    dotProduct_traceGram, dotProduct_traceGram, traceForm_apply, traceForm_apply, omegaE_swap,
    mul_neg, map_neg]

theorem traceGram_invariant (θ : extension (ν : k))
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (ν : k))) :
    ((rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL g) : GL (Fin 4) k) :
        Matrix (Fin 4) (Fin 4) k)ᵀ * traceGram ν Ψ θ *
      (rowSPi ν Ψ (Matrix.SpecialLinearGroup.toGL g) : GL (Fin 4) k) = traceGram ν Ψ θ := by
  apply matrix_eq_of_dotProduct
  intro v w
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    dotProduct_traceGram, dotProduct_traceGram, traceForm_apply, traceForm_apply,
    rowSPi_mulVec, rowSPi_mulVec, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  change Algebra.trace k (extension (ν : k)) (θ * omegaE ν ((g : Matrix _ _ _) *ᵥ Ψ.symm v)
    ((g : Matrix _ _ _) *ᵥ Ψ.symm w)) = _
  rw [omegaE_mulVec, g.2, one_mul]

theorem rowSPi_scalar_mulVec (θ : (extension (ν : k))ˣ) (v : Fin 4 → k) :
    Ψ.symm (((rowSPi ν Ψ (GeneralLinearGroup.scalar (Fin 2) θ) : GL (Fin 4) k) :
      Matrix (Fin 4) (Fin 4) k) *ᵥ v) = (θ : extension (ν : k)) • Ψ.symm v := by
  rw [rowSPi_mulVec, LinearEquiv.symm_apply_apply, GeneralLinearGroup.coe_scalar]
  funext i
  simp [Matrix.scalar_apply, mulVec_diagonal]

theorem traceGram_rowSU (θ : extension (ν : k)) :
    ((rowSU ν Ψ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)ᵀ * traceGram ν Ψ θ *
      (rowSU ν Ψ : GL (Fin 4) k) = (ν : k) • traceGram ν Ψ θ := by
  apply matrix_eq_of_dotProduct
  intro v w
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    dotProduct_traceGram, smul_mulVec, dotProduct_smul, dotProduct_traceGram, traceForm_apply,
    traceForm_apply, rowSU, rowSPi_scalar_mulVec, rowSPi_scalar_mulVec, smul_eq_mul]
  have key : θ * omegaE ν ((rootUnit ν : extension (ν : k)) • Ψ.symm v)
      ((rootUnit ν : extension (ν : k)) • Ψ.symm w) =
      (ν : k) • (θ * omegaE ν (Ψ.symm v) (Ψ.symm w)) := by
    have ht := extension_root_square (ν : k)
    simp only [omegaE, Pi.smul_apply, smul_eq_mul, coe_rootUnit]
    rw [Algebra.smul_def]
    linear_combination (θ * (Ψ.symm v 0 * Ψ.symm w 1 - Ψ.symm v 1 * Ψ.symm w 0)) * ht
  rw [key, LinearMap.map_smul_of_tower, smul_eq_mul]

theorem traceGram_eq (θ : (extension (ν : k))ˣ) :
    traceGram ν Ψ θ = ((rowSPi ν Ψ (GeneralLinearGroup.scalar (Fin 2) θ) : GL (Fin 4) k) :
      Matrix (Fin 4) (Fin 4) k)ᵀ * traceGram ν Ψ 1 := by
  apply matrix_eq_of_dotProduct
  intro v w
  conv_rhs => rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [dotProduct_traceGram, dotProduct_traceGram, traceForm_apply, traceForm_apply,
    rowSPi_scalar_mulVec, one_mul]
  congr 1
  simp only [omegaE, Pi.smul_apply, smul_eq_mul]
  ring

theorem det_rowSPi_scalar (θ : (extension (ν : k))ˣ) :
    ((rowSPi ν Ψ (GeneralLinearGroup.scalar (Fin 2) θ) : GL (Fin 4) k) :
      Matrix (Fin 4) (Fin 4) k).det = Algebra.norm k (θ : extension (ν : k)) ^ 2 := by
  rw [det_rowSPi, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

theorem det_traceGram_ne_zero [Fact (¬ IsSquare (ν : k))] (h2 : (2 : k) ≠ 0)
    {θ : extension (ν : k)} (hθ : θ ≠ 0) : (traceGram ν Ψ θ).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set y := Ψ.symm w with hydef
  have hy : y ≠ 0 := fun h => hw0 (by rw [← Ψ.apply_symm_apply w, ← hydef, h, map_zero])
  have hall : ∀ x : Fin 2 → extension (ν : k),
      Algebra.trace k (extension (ν : k)) (θ * omegaE ν x y) = 0 := by
    intro x
    have h1 := dotProduct_traceGram ν Ψ θ (Ψ x) w
    rw [hw, dotProduct_zero, traceForm_apply, LinearEquiv.symm_apply_apply] at h1
    exact h1.symm
  obtain ⟨x, hx⟩ : ∃ x, omegaE ν x y = θ⁻¹ := by
    by_cases h1 : y 1 = 0
    · have h0 : y 0 ≠ 0 := by
        intro h0
        apply hy
        funext i
        fin_cases i
        · exact h0
        · exact h1
      refine ⟨![0, -(θ⁻¹ / y 0)], ?_⟩
      simp only [omegaE, Matrix.cons_val_zero, Matrix.cons_val_one, h1]
      field_simp
      ring
    · refine ⟨![θ⁻¹ / y 1, 0], ?_⟩
      simp only [omegaE, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      ring
  have h3 := hall x
  rw [hx, mul_inv_cancel₀ hθ, ← map_one (algebraMap k (extension (ν : k))),
    Algebra.trace_algebraMap, extension_finrank, nsmul_eq_mul, Nat.cast_ofNat, mul_one] at h3
  exact h2 h3

end Trace

end Catalog7L4E

end CFSG.ComponentClassification.OddSelector
