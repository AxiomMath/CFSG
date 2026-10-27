module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceNorm

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

abbrev rightMul (g : SL(2, K)) : DeterminantIsometries K := specialRho (1, g)

theorem rightMul_apply (g : SL(2, K)) (M : Matrix (Fin 2) (Fin 2) K) :
    (rightMul g).val M = M * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  rw [specialRho_apply]
  simp

theorem rho_mul_rightMul_mul_inv (z : equalDeterminants K) (g : SL(2, K)) :
    rho z * rightMul g * (rho z)⁻¹ = rightMul (conjSL z.val.2 g) := by
  have h : z * specialPairs (1, g) * z⁻¹ = specialPairs (1, conjSL z.val.2 g) := by
    apply Subtype.ext
    apply Prod.ext
    · apply Units.ext
      change ((z.val.1 * Matrix.SpecialLinearGroup.toGL (1 : SL(2, K)) * z.val.1⁻¹ :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          ((Matrix.SpecialLinearGroup.toGL (1 : SL(2, K)) : GL (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)
      rw [map_one, mul_one, mul_inv_cancel]
    · apply Units.ext
      change ((z.val.2 * Matrix.SpecialLinearGroup.toGL g * z.val.2⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
          ((Matrix.SpecialLinearGroup.toGL (conjSL z.val.2 g) : GL (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)
      rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_conjSL]
  calc rho z * rightMul g * (rho z)⁻¹ = rho (z * specialPairs (1, g) * z⁻¹) := by
        rw [map_mul, map_mul, map_inv]
        rfl
    _ = rightMul (conjSL z.val.2 g) := by rw [h]; rfl

theorem leftMul_mul_rightMul (g g' : SL(2, K)) :
    leftMul g * rightMul g' = rightMul g' * leftMul g := by
  rw [← map_mul, ← map_mul]
  congr 1
  ext <;> simp

@[expose] def qGamMat (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (γ : DeterminantIsometries K) :
    Matrix (Fin 4) (Fin 4) K :=
  LinearMap.toMatrix' ((qEquiv h2 ha).symm.toLinearMap ∘ₗ
    γ.val.toLinearMap ∘ₗ (qEquiv h2 ha).toLinearMap)

theorem qGamMat_mulVec (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (γ : DeterminantIsometries K)
    (x : Fin 4 → K) :
    qGamMat h2 ha γ *ᵥ x = (qEquiv h2 ha).symm (γ.val (qEquiv h2 ha x)) := by
  rw [qGamMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem qGamMat_mul (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (γ γ' : DeterminantIsometries K) :
    qGamMat h2 ha (γ * γ') = qGamMat h2 ha γ * qGamMat h2 ha γ' := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, qGamMat_mulVec, qGamMat_mulVec, qGamMat_mulVec,
    LinearEquiv.apply_symm_apply]
  rfl

theorem qGamMat_one (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) : qGamMat h2 ha 1 = 1 := by
  refine (Matrix.toLin' (R := K)).injective (LinearMap.ext fun x => ?_)
  rw [Matrix.toLin'_apply, qGamMat_mulVec, Matrix.toLin'_one]
  change (qEquiv h2 ha).symm (qEquiv h2 ha x) = x
  rw [LinearEquiv.symm_apply_apply]

theorem qGamMat_isometry (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (γ : DeterminantIsometries K) :
    (qGamMat h2 ha γ)ᵀ * diagonal (qW a) * qGamMat h2 ha γ = diagonal (qW a) := by
  refine eq_of_forall_dotProduct_mulVec h2 ?_ (diagonal_transpose _) fun x => ?_
  · rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  · have e : x ⬝ᵥ ((qGamMat h2 ha γ)ᵀ * diagonal (qW a) * qGamMat h2 ha γ) *ᵥ x =
        (qGamMat h2 ha γ *ᵥ x) ⬝ᵥ diagonal (qW a) *ᵥ (qGamMat h2 ha γ *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        vecMul_transpose]
    rw [e, ← det_qEquiv h2 ha, ← det_qEquiv h2 ha, qGamMat_mulVec, LinearEquiv.apply_symm_apply,
      ← determinantForm_apply, ← determinantForm_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 γ.2 _

@[expose] def qGammaInv (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    DeterminantIsometries K →* CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha)) where
  toFun γ := ⟨⟨qGamMat h2 ha γ, qGamMat h2 ha γ⁻¹, by rw [← qGamMat_mul, mul_inv_cancel,
      qGamMat_one], by rw [← qGamMat_mul, inv_mul_cancel, qGamMat_one]⟩, by
    rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL]
    exact qGamMat_isometry h2 ha γ⟩
  map_one' := Subtype.ext (Units.ext (qGamMat_one h2 ha))
  map_mul' γ γ' := Subtype.ext (Units.ext (qGamMat_mul h2 ha γ γ'))

theorem coe_qGammaInv (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (γ : DeterminantIsometries K) :
    (((qGammaInv h2 ha γ : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha))) :
      GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = qGamMat h2 ha γ := rfl

theorem qGamma_qGammaInv (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (γ : DeterminantIsometries K) :
    qGamma h2 ha (qGammaInv h2 ha γ) = γ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro M
  obtain ⟨x, rfl⟩ := (qEquiv h2 ha).surjective M
  rw [qGamma_apply, coe_qGammaInv, qGamMat_mulVec, LinearEquiv.apply_symm_apply]

@[expose] def qLambdaR (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    SL(2, K) →* CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha)) :=
  (qGammaInv h2 ha).comp ((specialRho (K := K)).comp (MonoidHom.inr _ _))

theorem qGamma_qLambdaR (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    qGamma h2 ha (qLambdaR h2 ha g) = rightMul g :=
  qGamma_qGammaInv h2 ha _

theorem qLambdaR_injective (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    Function.Injective (qLambdaR h2 ha) := by
  intro g g' hgg
  have e := congrArg (qGamma h2 ha) hgg
  rw [qGamma_qLambdaR, qGamma_qLambdaR] at e
  have e1 := congrArg (fun γ : DeterminantIsometries K => γ.val 1) e
  simp only [rightMul_apply, Matrix.one_mul] at e1
  have : g⁻¹ = g'⁻¹ := Subtype.ext e1
  exact inv_injective this

theorem qLambda_mul_qLambdaR (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (g g' : SL(2, K)) :
    qLambda h2 ha g * qLambdaR h2 ha g' = qLambdaR h2 ha g' * qLambda h2 ha g := by
  apply qGamma_injective h2 ha
  rw [map_mul, map_mul, qGamma_qLambda, qGamma_qLambdaR, leftMul_mul_rightMul]

theorem qLambdaR_neg_one (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    qLambdaR h2 ha (-1) = qLambda h2 ha (-1) := by
  apply qGamma_injective h2 ha
  rw [qGamma_qLambda, qGamma_qLambdaR]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro M
  rw [leftMul_apply, rightMul_apply]
  have : ((-1 : SL(2, K))⁻¹ : SL(2, K)) = -1 := by
    rw [inv_eq_of_mul_eq_one_right]
    ext i j
    simp
  rw [this]
  simp

variable {d : ℕ}

variable (K) in
@[expose] def oSliceR (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0) :
    SL(2, K) →* GL (Fin d) K :=
  (embedGL4 K hd).comp ((Subgroup.subtype _).comp (qLambdaR h2 ha))

theorem coe_oSliceR (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0) (g : SL(2, K)) :
    ((oSliceR K h2 hd ha g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      embed4 K hd (((qLambdaR h2 ha g : CatalogueBGraphForm.isometryGroup 4 K
        (diagGL (qW_ne_zero ha))) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := rfl

theorem oSliceR_injective (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0) :
    Function.Injective (oSliceR K h2 hd ha) :=
  (embedGL4_injective hd).comp ((Subgroup.subtype_injective _).comp (qLambdaR_injective h2 ha))

theorem oSlice_mul_oSliceR (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0)
    (g g' : SL(2, K)) :
    oSlice K h2 hd ha g * oSliceR K h2 hd ha g' = oSliceR K h2 hd ha g' * oSlice K h2 hd ha g := by
  simp only [oSlice, oSliceR, MonoidHom.comp_apply, ← map_mul]
  rw [qLambda_mul_qLambdaR]

theorem oSliceR_neg_one (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0) :
    oSliceR K h2 hd ha (-1) = oSlice K h2 hd ha (-1) := by
  simp only [oSlice, oSliceR, MonoidHom.comp_apply, qLambdaR_neg_one]

theorem oSliceR_mem_oIsoBlock (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    oSliceR K h2 hd hW.ha g ∈ oIsoBlock K hw wSet := by
  rw [mem_oIsoBlock_iff]
  exact ⟨embedGL4_mem_iso hd hw hW.ha hW.hw4 (qLambdaR h2 hW.ha g).2,
    embed4_support hd _⟩

theorem oSliceR_mem_oBlock [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    oSliceR K h2 hd hW.ha g ∈ oBlock K hw wSet :=
  mem_commutator_of_perfect (CatalogueBGeneralLinear.specialLinear_perfect 2 K le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))) _ (oSliceR_mem_oIsoBlock h2 hd hw hW) g

theorem oSliceR_mem_derived [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    oSliceR K h2 hd hW.ha g ∈ matrixDerived (oQ (diagGL hw)) := by
  rw [matrixDerived_oQ h2 _ (diagGL_transpose hw)]
  exact oBlock_le hw wSet (oSliceR_mem_oBlock h2 hK4 hd hw hW g)

@[expose] def oSliceRH [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) :
    SL(2, K) →* matrixDerived (oQ (diagGL hw)) :=
  (oSliceR K h2 hd hW.ha).codRestrict _ (oSliceR_mem_derived h2 hK4 hd hw hW)

theorem coe_oSliceRH [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (g : SL(2, K)) :
    ((oSliceRH h2 hK4 hd hw hW g : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
      oSliceR K h2 hd hW.ha g := rfl

theorem oSliceRH_injective [Finite K] (h2 : (2 : K) ≠ 0) (hK4 : 4 ≤ Nat.card K) (hd : 4 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) :
    Function.Injective (oSliceRH h2 hK4 hd hw hW) := fun _ _ h =>
  oSliceR_injective h2 hd hW.ha (congrArg Subtype.val h)

theorem conj_oSliceR_of_rho (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {a : K} (ha : a ≠ 0)
    {h : GL (Fin d) K}
    (hc : (h : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * (h : Matrix (Fin d) (Fin d) K))
    {X : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha))}
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = blk4 hd h)
    (hXi : ((X⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk4 hd ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    {z : equalDeterminants K} (hz : qGamma h2 ha X = rho z) (g : SL(2, K)) :
    h * oSliceR K h2 hd ha g * h⁻¹ = oSliceR K h2 hd ha (conjSL z.val.2 g) := by
  have hhi : (h : Matrix (Fin d) (Fin d) K) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hih : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (h : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hci : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * embed4 K hd (-1) =
      embed4 K hd (-1) * ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
    commute_inv_of_commute hhi hih hc
  have key : X * qLambdaR h2 ha g * X⁻¹ = qLambdaR h2 ha (conjSL z.val.2 g) := by
    apply qGamma_injective h2 ha
    rw [map_mul, map_mul, map_inv, qGamma_qLambdaR, qGamma_qLambdaR, hz,
      rho_mul_rightMul_mul_inv]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_oSliceR, coe_oSliceR,
    (mul_embed4_mul h2 hd hhi hc hci _).1, ← hX, ← hXi]
  congr 1
  have := congrArg (fun Y : CatalogueBGraphForm.isometryGroup 4 K (diagGL (qW_ne_zero ha)) =>
    ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) key
  simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv] using this

theorem conj_oSliceR_of_mem (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) (X : oIsoBlock K hw wSet)
    {z : equalDeterminants K} (hz : qGamma h2 hW.ha (oBlkHom h2 hd hw hW X) = rho z)
    (g : SL(2, K)) :
    (X : GL (Fin d) K) * oSliceR K h2 hd hW.ha g * (X : GL (Fin d) K)⁻¹ =
      oSliceR K h2 hd hW.ha (conjSL z.val.2 g) :=
  conj_oSliceR_of_rho h2 hd hW.ha (commute_embed4_of_mem h2 hd hw X.2)
    (coe_oBlkHom h2 hd hw hW X) (coe_oBlkHom_inv h2 hd hw hW X) hz g

theorem oBlock_le_normalizer_R (h2 : (2 : K) ≠ 0) (hd : 4 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW hd w α a) :
    oBlock K hw wSet ≤ normalizer ((oSliceR K h2 hd hW.ha).range : Set (GL (Fin d) K)) := by
  have hc : ∀ X ∈ oIsoBlock K hw wSet, ∀ Y ∈ oIsoBlock K hw wSet, ∀ g,
      ⁅X, Y⁆ * oSliceR K h2 hd hW.ha g * ⁅X, Y⁆⁻¹ ∈ (oSliceR K h2 hd hW.ha).range := by
    intro X hX Y hY g
    set X' : oIsoBlock K hw wSet := ⟨X, hX⟩
    set Y' : oIsoBlock K hw wSet := ⟨Y, hY⟩
    have hmem := commutator_mem_leftRightImage (qGamma h2 hW.ha (oBlkHom h2 hd hw hW X'))
      (qGamma h2 hW.ha (oBlkHom h2 hd hw hW Y'))
    rw [← map_commutatorElement, ← map_commutatorElement] at hmem
    obtain ⟨z, hz⟩ := hmem
    have e := conj_oSliceR_of_mem h2 hd hw hW ⁅X', Y'⁆ hz.symm g
    exact ⟨_, e.symm⟩
  rw [oBlock, Subgroup.commutator_le]
  intro X hX Y hY
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, rfl⟩
    exact hc X hX Y hY x
  · intro hg
    obtain ⟨x, hx⟩ := hg
    have e := hc Y hY X hX x
    have e' : ⁅Y, X⁆ * oSliceR K h2 hd hW.ha x * ⁅Y, X⁆⁻¹ = g := by
      rw [hx, ← commutatorElement_inv X Y]
      group
    rwa [e'] at e

end CFSG.ComponentClassification.Burgoyne.O
