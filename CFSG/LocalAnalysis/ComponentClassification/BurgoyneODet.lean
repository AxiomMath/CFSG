module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthNormal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

@[expose] def qMat (a : K) (x : Fin 4 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![x 0 + x 2, a * x 1 - a * x 3; -x 1 - x 3, x 0 - x 2]

@[expose] def qVec (a : K) (M : Matrix (Fin 2) (Fin 2) K) : Fin 4 → K :=
  ![(M 0 0 + M 1 1) / 2, (M 0 1 / a - M 1 0) / 2, (M 0 0 - M 1 1) / 2,
    (-(M 0 1) / a - M 1 0) / 2]

theorem qVec_qMat (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (x : Fin 4 → K) :
    qVec a (qMat a x) = x := by
  funext i
  fin_cases i <;> simp [qVec, qMat] <;> field_simp <;> ring

theorem qMat_qVec (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (M : Matrix (Fin 2) (Fin 2) K) :
    qMat a (qVec a M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qVec, qMat] <;> field_simp <;> ring

@[expose] def qEquiv (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    (Fin 4 → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun := qMat a
  invFun := qVec a
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qMat] <;> ring
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qMat] <;> ring
  left_inv := qVec_qMat h2 ha
  right_inv := qMat_qVec h2 ha

theorem qEquiv_apply (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (x : Fin 4 → K) :
    qEquiv h2 ha x = qMat a x := rfl

@[expose] def qW (a : K) : Fin 4 → K := ![1, a, -1, -a]

theorem qW_ne_zero {a : K} (ha : a ≠ 0) : ∀ i, qW a i ≠ 0 := by
  intro i
  fin_cases i <;> simp [qW, ha]

theorem det_qEquiv (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (x : Fin 4 → K) :
    (qEquiv h2 ha x).det = x ⬝ᵥ (diagonal (qW a)) *ᵥ x := by
  rw [qEquiv_apply, qMat, det_fin_two_of]
  simp [qW, dotProduct, Fin.sum_univ_four, mulVec, diagonal]
  ring

@[expose] def qGamma (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    CatalogueBGraphForm.isometryGroup 4 K (PSL.diagGL (qW_ne_zero ha)) →*
      DeterminantIsometries K where
  toFun X := ⟨(qEquiv h2 ha).symm.trans ((matrixLinearEquiv (X : GL (Fin 4) K)).trans
      (qEquiv h2 ha)), TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun M => by
    rw [determinantForm_apply, determinantForm_apply]
    change (qEquiv h2 ha (matrixLinearEquiv (X : GL (Fin 4) K) ((qEquiv h2 ha).symm M))).det = _
    rw [det_qEquiv, matrixLinearEquiv_apply]
    have hX := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 X.2
    rw [PSL.coe_diagGL] at hX
    set v := (qEquiv h2 ha).symm M
    have e : v ⬝ᵥ (((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * diagonal (qW a) *
          ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *ᵥ v =
        (((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) ⬝ᵥ diagonal (qW a) *ᵥ
        (((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        vecMul_transpose]
    rw [← e, hX, ← det_qEquiv h2 ha v, LinearEquiv.apply_symm_apply]⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro M
    change qEquiv h2 ha ((1 : Matrix (Fin 4) (Fin 4) K) *ᵥ (qEquiv h2 ha).symm M) = M
    rw [one_mulVec, LinearEquiv.apply_symm_apply]
  map_mul' X Y := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro M
    change qEquiv h2 ha (((X * Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
      (qEquiv h2 ha).symm M) = qEquiv h2 ha (((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
        (qEquiv h2 ha).symm (qEquiv h2 ha (((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          (qEquiv h2 ha).symm M)))
    rw [LinearEquiv.symm_apply_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem qGamma_apply (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0)
    (X : CatalogueBGraphForm.isometryGroup 4 K (PSL.diagGL (qW_ne_zero ha)))
    (x : Fin 4 → K) :
    (qGamma h2 ha X : DeterminantIsometries K).val (qEquiv h2 ha x) =
      qEquiv h2 ha (((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x) := by
  change qEquiv h2 ha (_ *ᵥ (qEquiv h2 ha).symm (qEquiv h2 ha x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem qGamma_injective (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    Function.Injective (qGamma h2 ha) := by
  intro X Y hXY
  apply Subtype.ext
  apply Units.ext
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  have e := congrArg (fun g : DeterminantIsometries K => g.val (qEquiv h2 ha x)) hXY
  simp only [qGamma_apply] at e
  exact (qEquiv h2 ha).injective e

abbrev leftMul (g : SL(2, K)) : DeterminantIsometries K := specialRho (g, 1)

theorem leftMul_apply (g : SL(2, K)) (M : Matrix (Fin 2) (Fin 2) K) :
    (leftMul g).val M = (g : Matrix (Fin 2) (Fin 2) K) * M := by
  rw [specialRho_apply]
  simp

theorem leftMul_hom : (fun g : SL(2, K) => leftMul g) = (specialRho (K := K)).comp
    (MonoidHom.inl _ _) := rfl

@[expose] def conjSL (A : GL (Fin 2) K) (g : SL(2, K)) : SL(2, K) :=
  ⟨(A : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
    ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
      rw [Matrix.det_mul, Matrix.det_mul, g.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem coe_conjSL (A : GL (Fin 2) K) (g : SL(2, K)) :
    ((conjSL A g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) *
        ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := rfl

theorem rho_mul_leftMul_mul_inv (z : equalDeterminants K) (g : SL(2, K)) :
    rho z * leftMul g * (rho z)⁻¹ = leftMul (conjSL z.val.1 g) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro M
  change (rho z).val ((leftMul g).val ((rho z)⁻¹.val M)) = (leftMul (conjSL z.val.1 g)).val M
  rw [leftMul_apply, leftMul_apply, coe_conjSL, ← map_inv, rho_apply, rho_apply]
  simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv, inv_inv]
  simp only [Matrix.mul_assoc, ← Units.val_mul]
  rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]

@[expose] def qLamMat (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    Matrix (Fin 4) (Fin 4) K :=
  LinearMap.toMatrix' ((qEquiv h2 ha).symm.toLinearMap ∘ₗ
    (leftMul g).val.toLinearMap ∘ₗ (qEquiv h2 ha).toLinearMap)

theorem qLamMat_mulVec (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g : SL(2, K))
    (x : Fin 4 → K) :
    qLamMat h2 ha g *ᵥ x = (qEquiv h2 ha).symm ((g : Matrix (Fin 2) (Fin 2) K) *
      qEquiv h2 ha x) := by
  rw [qLamMat, LinearMap.toMatrix'_mulVec]
  change (qEquiv h2 ha).symm ((leftMul g).val (qEquiv h2 ha x)) = _
  rw [leftMul_apply]

theorem qLamMat_mul (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g g' : SL(2, K)) :
    qLamMat h2 ha (g * g') = qLamMat h2 ha g * qLamMat h2 ha g' := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, qLamMat_mulVec, qLamMat_mulVec, qLamMat_mulVec,
    LinearEquiv.apply_symm_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem qLamMat_one (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) : qLamMat h2 ha 1 = 1 := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, qLamMat_mulVec, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
    LinearEquiv.symm_apply_apply, Matrix.toLin'_one]
  rfl

theorem qLamMat_isometry (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    (qLamMat h2 ha g)ᵀ * diagonal (qW a) * qLamMat h2 ha g = diagonal (qW a) := by
  refine eq_of_forall_dotProduct_mulVec h2 ?_ (diagonal_transpose _) fun x => ?_
  · rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  · have e : x ⬝ᵥ ((qLamMat h2 ha g)ᵀ * diagonal (qW a) * qLamMat h2 ha g) *ᵥ x =
        (qLamMat h2 ha g *ᵥ x) ⬝ᵥ diagonal (qW a) *ᵥ (qLamMat h2 ha g *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        vecMul_transpose]
    rw [e, ← det_qEquiv h2 ha, ← det_qEquiv h2 ha, qLamMat_mulVec, LinearEquiv.apply_symm_apply,
      Matrix.det_mul, g.2, one_mul]

@[expose] def qLambda (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    SL(2, K) →* CatalogueBGraphForm.isometryGroup 4 K (PSL.diagGL (qW_ne_zero ha)) where
  toFun g := ⟨⟨qLamMat h2 ha g, qLamMat h2 ha g⁻¹, by rw [← qLamMat_mul, mul_inv_cancel,
      qLamMat_one], by rw [← qLamMat_mul, inv_mul_cancel, qLamMat_one]⟩, by
    rw [CatalogueBGraphForm.mem_isometryGroup, PSL.coe_diagGL]
    exact qLamMat_isometry h2 ha g⟩
  map_one' := Subtype.ext (Units.ext (qLamMat_one h2 ha))
  map_mul' g g' := Subtype.ext (Units.ext (qLamMat_mul h2 ha g g'))

theorem coe_qLambda (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    (((qLambda h2 ha g : CatalogueBGraphForm.isometryGroup 4 K (PSL.diagGL (qW_ne_zero ha))) :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = qLamMat h2 ha g := rfl

theorem qGamma_qLambda (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    qGamma h2 ha (qLambda h2 ha g) = leftMul g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro M
  obtain ⟨x, rfl⟩ := (qEquiv h2 ha).surjective M
  rw [qGamma_apply, coe_qLambda, qLamMat_mulVec, LinearEquiv.apply_symm_apply, leftMul_apply]

theorem qLambda_injective (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    Function.Injective (qLambda h2 ha) := by
  intro g g' hgg
  have e := congrArg (qGamma h2 ha) hgg
  rw [qGamma_qLambda, qGamma_qLambda] at e
  apply Subtype.ext
  have e1 := congrArg (fun γ : DeterminantIsometries K => γ.val 1) e
  simpa [leftMul_apply] using e1

theorem qLambda_neg_one (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    (((qLambda h2 ha (-1) : CatalogueBGraphForm.isometryGroup 4 K (PSL.diagGL (qW_ne_zero ha))) :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, coe_qLambda, qLamMat_mulVec, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mul, Matrix.one_mul, map_neg,
    LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, neg_mulVec, one_mulVec]

theorem commutator_mem_leftRightImage (g h : DeterminantIsometries K) :
    ⁅g, h⁆ ∈ leftRightImage K := by
  have hcyc : IsCyclic (DeterminantIsometries K ⧸ leftRightImage K) :=
    isCyclic_of_card_dvd_prime (p := 2) leftRightImage_index_dvd_two
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact (IsCyclic.commGroup (α := DeterminantIsometries K ⧸ leftRightImage K)).mul_comm _ _

theorem mem_leftRightImage_of_odd {g : DeterminantIsometries K} {m : ℕ} (hm : Odd m)
    (hg : g ^ m = 1) : g ∈ leftRightImage K := by
  have hN : (leftRightImage K).Normal := inferInstance
  have h2 : g ^ 2 ∈ leftRightImage K := by
    have hi := Subgroup.pow_index_mem (leftRightImage K) g
    rcases (Nat.dvd_prime Nat.prime_two).1 (leftRightImage_index_dvd_two (K := K)) with h | h
    · rw [h, pow_one] at hi
      exact pow_mem hi 2
    · rwa [h] at hi
  obtain ⟨k, rfl⟩ := hm
  have e : g = g ^ (2 * k + 1) * ((g ^ 2) ^ k)⁻¹ := by group
  rw [e, hg, one_mul]
  exact inv_mem (pow_mem h2 k)

end CFSG.ComponentClassification.Burgoyne.O
