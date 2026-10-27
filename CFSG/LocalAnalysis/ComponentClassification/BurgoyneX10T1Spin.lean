module

public import CFSG.LieType.Universal.Spin.Chevalley.Frame

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG.LieType.Universal.Spin QuadraticMap Matrix

variable {K : Type} [Field K] {σ : Type} {Q : QuadraticForm K (σ → K)} {n : ℕ}

@[expose] def eichlerOp (F : HypFrame Q n) (i j : Fin n) (s t : Bool) :
    (σ → K) →ₗ[K] (σ → K) :=
  LinearMap.smulRight ((polarBilin Q).flip (F.vec j t)) (F.vec i s) -
    LinearMap.smulRight ((polarBilin Q).flip (F.vec i s)) (F.vec j t)

theorem eichlerOp_apply (F : HypFrame Q n) (i j : Fin n) (s t : Bool) (v : σ → K) :
    eichlerOp F i j s t v = polar Q v (F.vec j t) • F.vec i s - polar Q v (F.vec i s) • F.vec j t :=
  rfl

theorem spinAction_longRoot_eq (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (c : K) :
    (spinAction Q (F.longRoot hij s t (.ofAdd c)) : (σ → K) →ₗ[K] σ → K) =
      LinearMap.id + c • eichlerOp F i j s t := by
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.coe_coe, F.spinAction_longRoot hij s t c v, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.smul_apply, eichlerOp_apply, smul_sub, smul_smul, smul_smul]
  abel

variable [Fintype σ] [DecidableEq σ]

@[expose] def eichlerMatrix (F : HypFrame Q n) (i j : Fin n) (s t : Bool) : Matrix σ σ K :=
  LinearMap.toMatrix' (eichlerOp F i j s t)

theorem spinMatrix_longRoot (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    (spinMatrix Q (F.longRoot hij s t (.ofAdd c)) : Matrix σ σ K) =
      1 + c • eichlerMatrix F i j s t := by
  rw [coe_spinMatrix, spinAction_longRoot_eq F hij s t c, map_add, map_smul,
    LinearMap.toMatrix'_id, eichlerMatrix]

theorem eichlerMatrix_mul_self (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    eichlerMatrix F i j s t * eichlerMatrix F i j s t = 0 := by
  rw [eichlerMatrix, ← LinearMap.toMatrix'_comp]
  have h0 : eichlerOp F i j s t ∘ₗ eichlerOp F i j s t = 0 := by
    refine LinearMap.ext fun v => ?_
    have huw : polar Q (F.vec i s) (F.vec j t) = 0 := F.polar_vec_of_ne hij s t
    have hwu : polar Q (F.vec j t) (F.vec i s) = 0 := F.polar_vec_of_ne hij.symm t s
    have huu : polar Q (F.vec i s) (F.vec i s) = 0 := by
      rw [polar_self, F.map_vec, smul_zero]
    have hww : polar Q (F.vec j t) (F.vec j t) = 0 := by
      rw [polar_self, F.map_vec, smul_zero]
    rw [LinearMap.comp_apply, eichlerOp_apply, eichlerOp_apply, LinearMap.zero_apply]
    simp only [polar_sub_left, polar_smul_left, huw, hwu, huu, hww, smul_zero, sub_self,
      zero_smul]
  rw [h0, map_zero]

theorem eichlerMatrix_ne_zero (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    eichlerMatrix F i j s t ≠ 0 := by
  intro h0
  have h1 : eichlerOp F i j s t (F.vec j (!t)) = F.vec i s := by
    rw [eichlerOp_apply, polar_comm, F.polar_vec_not, one_smul,
      F.polar_vec_of_ne hij.symm, zero_smul, sub_zero]
  have h2 : eichlerOp F i j s t = 0 := by
    rw [← Matrix.toLin'_toMatrix' (eichlerOp F i j s t)]
    change Matrix.toLin' (eichlerMatrix F i j s t) = 0
    rw [h0, map_zero]
  rw [h2, LinearMap.zero_apply] at h1
  have h3 := F.polar_vec_not i s
  rw [← h1, polar_zero_left] at h3
  exact zero_ne_one h3

theorem spinMatrix_conj_longRoot (F : HypFrame Q n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (y : spinGroup Q) (c : K) :
    (spinMatrix Q (y * F.longRoot hij s t (.ofAdd c) * y⁻¹) : Matrix σ σ K) =
      1 + c • ((spinMatrix Q y : Matrix σ σ K) * eichlerMatrix F i j s t *
        ((spinMatrix Q y)⁻¹ : GL σ K)) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, spinMatrix_longRoot F hij s t c,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conj_mul_self_eq_zero {N : Matrix σ σ K} (hN : N * N = 0) (M : GL σ K) :
    ((M : Matrix σ σ K) * N * (M⁻¹ : GL σ K)) * ((M : Matrix σ σ K) * N * (M⁻¹ : GL σ K)) = 0 := by
  have h : ((M⁻¹ : GL σ K) : Matrix σ σ K) * (M : Matrix σ σ K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((M : Matrix σ σ K) * N * (M⁻¹ : GL σ K)) * ((M : Matrix σ σ K) * N * (M⁻¹ : GL σ K)) =
      (M : Matrix σ σ K) * (N * (((M⁻¹ : GL σ K) : Matrix σ σ K) * (M : Matrix σ σ K)) * N) *
        (M⁻¹ : GL σ K) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_one, hN, Matrix.mul_zero, Matrix.zero_mul]

theorem conj_ne_zero {N : Matrix σ σ K} (hN : N ≠ 0) (M : GL σ K) :
    (M : Matrix σ σ K) * N * (M⁻¹ : GL σ K) ≠ 0 := by
  intro h
  apply hN
  have h1 : ((M⁻¹ : GL σ K) : Matrix σ σ K) * ((M : Matrix σ σ K) * N * (M⁻¹ : GL σ K)) *
      (M : Matrix σ σ K) = N := by
    have h2 : ((M⁻¹ : GL σ K) : Matrix σ σ K) * (M : Matrix σ σ K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [← h1, h, Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype σ] in
theorem reindex_one_add_smul {d : ℕ} (e : σ ≃ Fin d) (N : Matrix σ σ K) (c : K) :
    Matrix.reindex e e (1 + c • N) = 1 + c • Matrix.reindex e e N := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply]
  ext a b
  simp [Matrix.one_apply, e.symm.injective.eq_iff]

omit [DecidableEq σ] in
theorem reindex_mul_self_eq_zero {d : ℕ} (e : σ ≃ Fin d) {N : Matrix σ σ K} (hN : N * N = 0) :
    Matrix.reindex e e N * Matrix.reindex e e N = 0 := by
  rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv N N e.symm e.symm e.symm, hN]
  rfl

omit [Fintype σ] [DecidableEq σ] in
theorem reindex_ne_zero {d : ℕ} (e : σ ≃ Fin d) {N : Matrix σ σ K} (hN : N ≠ 0) :
    Matrix.reindex e e N ≠ 0 := by
  intro h
  apply hN
  ext a b
  have := congrFun (congrFun h (e a)) (e b)
  simpa [Matrix.reindex_apply] using this

end CFSG.ComponentClassification.Burgoyne.X10
