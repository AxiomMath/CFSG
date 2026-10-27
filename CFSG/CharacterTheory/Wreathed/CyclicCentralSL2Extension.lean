module

public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover

public noncomputable section
namespace CFSG.Wreathed.CyclicCentralSL2Extension
open Matrix
universe u
variable (F : Type u) [Field F]

@[expose] def nonsquareMatrix (b : Fˣ) : GeneralLinearGroup (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -(b : F); 1, 0] (by
    simp [Matrix.det_fin_two_of])

theorem nonsquareMatrix_val (b : Fˣ) :
    (nonsquareMatrix F b : Matrix (Fin 2) (Fin 2) F) = !![0, -(b : F); 1, 0] := rfl

@[expose] def matrixConjugation : GeneralLinearGroup (Fin 2) F →*
    MulAut (SpecialLinearGroup (Fin 2) F) :=
  (MulAut.congr (SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)).symm).toMonoidHom.comp
    (MulAut.conjNormal (H := (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) F →* Fˣ).ker))

theorem matrixConjugation_toGL (B : GeneralLinearGroup (Fin 2) F)
    (X : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL (matrixConjugation F B X) =
      B * SpecialLinearGroup.toGL X * B⁻¹ := by
  change ((SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F))
    ((SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)).symm
      ((MulAut.conjNormal (H := (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) F →* Fˣ).ker) B)
        ((SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := F)) X)))).val = _
  rw [MulEquiv.apply_symm_apply, MulAut.conjNormal_apply]
  rfl

@[expose] def beta (b : Fˣ) : MulAut (SpecialLinearGroup (Fin 2) F) :=
  matrixConjugation F (nonsquareMatrix F b)

theorem beta_toGL (b : Fˣ) (X : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL (beta F b X) =
      nonsquareMatrix F b * SpecialLinearGroup.toGL X * (nonsquareMatrix F b)⁻¹ :=
  matrixConjugation_toGL F _ X

theorem nonsquareMatrix_square (b : Fˣ) :
    nonsquareMatrix F b ^ 2 = GeneralLinearGroup.scalar (Fin 2) (-b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, nonsquareMatrix, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrixConjugation_scalar (c : Fˣ) :
    matrixConjugation F (GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
  apply MulEquiv.ext
  intro X
  apply SpecialLinearGroup.toGL_injective
  rw [matrixConjugation_toGL]
  change GeneralLinearGroup.scalar (Fin 2) c * SpecialLinearGroup.toGL X *
    (GeneralLinearGroup.scalar (Fin 2) c)⁻¹ = SpecialLinearGroup.toGL X
  have hc : GeneralLinearGroup.scalar (Fin 2) c ∈
      Subgroup.center (GeneralLinearGroup (Fin 2) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [← Subgroup.mem_center_iff.mp hc (SpecialLinearGroup.toGL X)]
  group

theorem beta_square (b : Fˣ) : beta F b ^ 2 = 1 := by
  rw [beta, ← map_pow, nonsquareMatrix_square, matrixConjugation_scalar]

theorem beta_minusIdentity (b : Fˣ) :
    beta F b (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  apply SpecialLinearGroup.toGL_injective
  rw [beta_toGL]
  have hc : SpecialLinearGroup.toGL
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) ∈
      Subgroup.center (GeneralLinearGroup (Fin 2) F) :=
    (SpecialLinearGroup.toGL_mem_center_iff _).mpr
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_mem_center F)
  rw [Subgroup.mem_center_iff.mp hc (nonsquareMatrix F b)]
  group

@[expose] def cyclicAction (b : Fˣ) (m : ℕ) (hm : 0 < m) :
    Multiplicative (ZMod (2 * m)) →* MulAut (SpecialLinearGroup (Fin 2) F) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  refine {
    toFun := fun j => beta F b ^ j.toAdd.val
    map_one' := by simp
    map_mul' := ?_ }
  intro j k
  have hperiod : beta F b ^ (2 * m) = 1 := by
    rw [pow_mul, beta_square, one_pow]
  simp only [toAdd_mul, ZMod.val_add]
  rw [← pow_eq_pow_mod _ hperiod, pow_add]

theorem cyclicAction_natCast (b : Fˣ) (m : ℕ) (hm : 0 < m) (j : ℕ) :
    cyclicAction F b m hm (Multiplicative.ofAdd (j : ZMod (2 * m))) = beta F b ^ j := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have hperiod : beta F b ^ (2 * m) = 1 := by
    rw [pow_mul, beta_square, one_pow]
  change beta F b ^ (j : ZMod (2 * m)).val = _
  rw [ZMod.val_natCast]
  exact (pow_eq_pow_mod j hperiod).symm

abbrev PairGroup (b : Fˣ) (m : ℕ) (hm : 0 < m) :=
  SpecialLinearGroup (Fin 2) F ⋊[cyclicAction F b m hm] Multiplicative (ZMod (2 * m))

@[expose] def pair (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) : PairGroup F b m hm :=
  ⟨X, Multiplicative.ofAdd j⟩

theorem pair_mul (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (X Y : SpecialLinearGroup (Fin 2) F) (j k : ZMod (2 * m)) :
    pair F b m hm X j * pair F b m hm Y k =
      pair F b m hm (X * cyclicAction F b m hm (Multiplicative.ofAdd j) Y) (j + k) := rfl

@[expose] def pairEquiv (b : Fˣ) (m : ℕ) (hm : 0 < m) :
    PairGroup F b m hm ≃ SpecialLinearGroup (Fin 2) F × ZMod (2 * m) where
  toFun v := (v.left, v.right.toAdd)
  invFun v := pair F b m hm v.1 v.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem pair_mul_explicit (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (X Y : SpecialLinearGroup (Fin 2) F) (j k : ZMod (2 * m)) :
    pair F b m hm X j * pair F b m hm Y k =
      pair F b m hm (X * (beta F b ^ j.val) Y) (j + k) := rfl

@[expose] def diagonalInvolution (b : Fˣ) (m : ℕ) (hm : 0 < m) : PairGroup F b m hm :=
  pair F b m hm (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) (m : ZMod (2 * m))

theorem diagonalInvolution_mem_center (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    diagonalInvolution F b m hm ∈ Subgroup.center (PairGroup F b m hm) := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  have hmid : cyclicAction F b m hm (Multiplicative.ofAdd (m : ZMod (2 * m))) = 1 := by
    rw [cyclicAction_natCast]
    obtain ⟨k, hk⟩ := heven
    rw [hk, ← two_mul, pow_mul, beta_square, one_pow]
  have hfix : cyclicAction F b m hm y.right
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
        CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
    change (beta F b ^ y.right.toAdd.val) _ = _
    induction y.right.toAdd.val with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, beta_minusIdentity]
      exact ih
  apply SemidirectProduct.ext
  · change y.left * cyclicAction F b m hm y.right
        (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F *
        cyclicAction F b m hm (Multiplicative.ofAdd (m : ZMod (2 * m))) y.left
    rw [hfix, hmid, MulAut.one_apply]
    exact Subgroup.mem_center_iff.mp
      (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_mem_center F) y.left
  · exact mul_comm _ _

theorem diagonalInvolution_square (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    diagonalInvolution F b m hm ^ 2 = 1 := by
  have hmid : cyclicAction F b m hm (Multiplicative.ofAdd (m : ZMod (2 * m))) = 1 := by
    rw [cyclicAction_natCast]
    obtain ⟨k, hk⟩ := heven
    rw [hk, ← two_mul, pow_mul, beta_square, one_pow]
  rw [pow_two]
  apply SemidirectProduct.ext
  · change CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F *
      cyclicAction F b m hm (Multiplicative.ofAdd (m : ZMod (2 * m)))
        (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) = 1
    rw [hmid, MulAut.one_apply, ← pow_two,
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_square]
  · apply Multiplicative.toAdd.injective
    change (m : ZMod (2 * m)) + (m : ZMod (2 * m)) = 0
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using ZMod.natCast_self (2 * m)

theorem diagonalInvolution_ne_one (b : Fˣ) (m : ℕ) (hm : 0 < m) :
    diagonalInvolution F b m hm ≠ 1 := by
  intro h
  have hright := congrArg (fun g : PairGroup F b m hm => g.right.toAdd) h
  have hv := congrArg ZMod.val hright
  change (m : ZMod (2 * m)).val = (0 : ZMod (2 * m)).val at hv
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
  omega

theorem diagonalInvolution_order (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    orderOf (diagonalInvolution F b m hm) = 2 :=
  orderOf_eq_prime (diagonalInvolution_square F b m hm heven)
    (diagonalInvolution_ne_one F b m hm)

@[expose] def diagonalKernel (b : Fˣ) (m : ℕ) (hm : 0 < m) (_heven : Even m) :
    Subgroup (PairGroup F b m hm) := Subgroup.zpowers (diagonalInvolution F b m hm)

theorem diagonalKernel_le_center (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    diagonalKernel F b m hm heven ≤ Subgroup.center (PairGroup F b m hm) :=
  Subgroup.zpowers_le.mpr (diagonalInvolution_mem_center F b m hm heven)

instance diagonalKernel_normal (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    (diagonalKernel F b m hm heven).Normal :=
  Subgroup.normal_of_le_center (diagonalKernel_le_center F b m hm heven)

theorem diagonalKernel_card (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    Nat.card (diagonalKernel F b m hm heven) = 2 := by
  rw [diagonalKernel, Nat.card_zpowers, diagonalInvolution_order F b m hm heven]

abbrev CentralExtension (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :=
  PairGroup F b m hm ⧸ diagonalKernel F b m hm heven

@[expose] def quotientClass (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    CentralExtension F b m hm heven :=
  QuotientGroup.mk' (diagonalKernel F b m hm heven) (pair F b m hm X j)

@[expose] def specialInclusion (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    SpecialLinearGroup (Fin 2) F →* CentralExtension F b m hm heven :=
  (QuotientGroup.mk' (diagonalKernel F b m hm heven)).comp SemidirectProduct.inl

theorem specialInclusion_apply (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (X : SpecialLinearGroup (Fin 2) F) :
    specialInclusion F b m hm heven X = quotientClass F b m hm heven X 0 := rfl

@[expose] def cyclicGenerator (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m) :
    CentralExtension F b m hm heven := quotientClass F b m hm heven 1 1

@[expose] def fieldSL (sigma : F ≃+* F) : MulAut (SpecialLinearGroup (Fin 2) F) where
  toFun := SpecialLinearGroup.map sigma.toRingHom
  invFun := SpecialLinearGroup.map sigma.symm.toRingHom
  left_inv X := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact sigma.symm_apply_apply (X i j)
  right_inv X := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact sigma.apply_symm_apply (X i j)
  map_mul' := (SpecialLinearGroup.map sigma.toRingHom).map_mul

theorem fieldSL_apply (sigma : F ≃+* F) (X : SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    fieldSL F sigma X i j = sigma (X i j) := rfl

theorem fieldSL_toGL (sigma : F ≃+* F) (X : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL (fieldSL F sigma X) =
      GeneralLinearGroup.map sigma.toRingHom (SpecialLinearGroup.toGL X) := by
  apply Units.ext
  ext i j
  rfl

theorem field_map_nonsquareMatrix (b : Fˣ) (sigma : F ≃+* F) (hb : sigma (b : F) = b) :
    GeneralLinearGroup.map sigma.toRingHom (nonsquareMatrix F b) = nonsquareMatrix F b := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, nonsquareMatrix_val, hb]

theorem fieldSL_beta (b : Fˣ) (sigma : F ≃+* F) (hb : sigma (b : F) = b)
    (X : SpecialLinearGroup (Fin 2) F) :
    fieldSL F sigma (beta F b X) = beta F b (fieldSL F sigma X) := by
  apply SpecialLinearGroup.toGL_injective
  rw [fieldSL_toGL, beta_toGL, map_mul, map_mul, map_inv,
    field_map_nonsquareMatrix F b sigma hb, beta_toGL, fieldSL_toGL]

theorem fieldSL_cyclicAction (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (sigma : F ≃+* F) (hb : sigma (b : F) = b)
    (j : Multiplicative (ZMod (2 * m))) (X : SpecialLinearGroup (Fin 2) F) :
    fieldSL F sigma (cyclicAction F b m hm j X) =
      cyclicAction F b m hm j (fieldSL F sigma X) := by
  change fieldSL F sigma ((beta F b ^ j.toAdd.val) X) =
    (beta F b ^ j.toAdd.val) (fieldSL F sigma X)
  induction j.toAdd.val generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, fieldSL_beta F b sigma hb]

theorem fieldSL_minusIdentity (sigma : F ≃+* F) :
    fieldSL F sigma (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change sigma (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F i j) =
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity]

@[expose] def fieldPair (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (sigma : F ≃+* F) (hb : sigma (b : F) = b) : MulAut (PairGroup F b m hm) :=
  SemidirectProduct.congr (fieldSL F sigma)
    (MulEquiv.refl (Multiplicative (ZMod (2 * m)))) (fun j => by
      apply MulEquiv.ext
      intro X
      exact fieldSL_cyclicAction F b m hm sigma hb j X)

theorem fieldPair_pair (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (sigma : F ≃+* F) (hb : sigma (b : F) = b)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    fieldPair F b m hm sigma hb (pair F b m hm X j) =
      pair F b m hm (fieldSL F sigma X) j := rfl

theorem fieldPair_diagonalInvolution (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (sigma : F ≃+* F) (hb : sigma (b : F) = b) :
    fieldPair F b m hm sigma hb (diagonalInvolution F b m hm) =
      diagonalInvolution F b m hm := by
  rw [diagonalInvolution, fieldPair_pair, fieldSL_minusIdentity]

theorem fieldPair_diagonalKernel (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (sigma : F ≃+* F) (hb : sigma (b : F) = b) :
    (diagonalKernel F b m hm heven).map
      (fieldPair F b m hm sigma hb : PairGroup F b m hm →* PairGroup F b m hm) =
      diagonalKernel F b m hm heven := by
  rw [diagonalKernel, MonoidHom.map_zpowers]
  change Subgroup.zpowers (fieldPair F b m hm sigma hb (diagonalInvolution F b m hm)) = _
  rw [fieldPair_diagonalInvolution]

@[expose] def fieldQuotient (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (sigma : F ≃+* F) (hb : sigma (b : F) = b) :
    MulAut (CentralExtension F b m hm heven) :=
  QuotientGroup.congr (diagonalKernel F b m hm heven) (diagonalKernel F b m hm heven)
    (fieldPair F b m hm sigma hb) (fieldPair_diagonalKernel F b m hm heven sigma hb)

theorem fieldQuotient_quotientClass (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (sigma : F ≃+* F) (hb : sigma (b : F) = b)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    fieldQuotient F b m hm heven sigma hb (quotientClass F b m hm heven X j) =
      quotientClass F b m hm heven (fieldSL F sigma X) j := by
  rw [fieldQuotient, quotientClass, QuotientGroup.congr_mk', fieldPair_pair]
  rfl

theorem fieldSL_one : fieldSL F (1 : F ≃+* F) = 1 := by
  apply MulEquiv.ext
  intro X
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

theorem fieldSL_mul (sigma tau : F ≃+* F) :
    fieldSL F (sigma * tau) = fieldSL F sigma * fieldSL F tau := by
  apply MulEquiv.ext
  intro X
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

theorem fieldQuotient_one (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (hb : (1 : F ≃+* F) (b : F) = b) :
    fieldQuotient F b m hm heven 1 hb = 1 := by
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H v =>
    change fieldQuotient F b m hm heven 1 hb
      (quotientClass F b m hm heven v.left v.right.toAdd) =
        quotientClass F b m hm heven v.left v.right.toAdd
    rw [fieldQuotient_quotientClass, fieldSL_one, MulAut.one_apply]

theorem fieldQuotient_mul (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (sigma tau : F ≃+* F) (hsigma : sigma (b : F) = b) (htau : tau (b : F) = b)
    (hmul : (sigma * tau) (b : F) = b) :
    fieldQuotient F b m hm heven (sigma * tau) hmul =
      fieldQuotient F b m hm heven sigma hsigma * fieldQuotient F b m hm heven tau htau := by
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H v =>
    change fieldQuotient F b m hm heven (sigma * tau) hmul
      (quotientClass F b m hm heven v.left v.right.toAdd) =
        (fieldQuotient F b m hm heven sigma hsigma *
          fieldQuotient F b m hm heven tau htau)
          (quotientClass F b m hm heven v.left v.right.toAdd)
    rw [MulAut.mul_apply, fieldQuotient_quotientClass, fieldQuotient_quotientClass,
      fieldQuotient_quotientClass, fieldSL_mul, MulAut.mul_apply]

@[expose] def fieldAction (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b) :
    Sigma →* MulAut (CentralExtension F b m hm heven) where
  toFun sigma := fieldQuotient F b m hm heven sigma (hSigma sigma sigma.property)
  map_one' := fieldQuotient_one F b m hm heven _
  map_mul' sigma tau := fieldQuotient_mul F b m hm heven sigma tau
    (hSigma sigma sigma.property) (hSigma tau tau.property) (hSigma _ (sigma * tau).property)

theorem fieldAction_quotientClass (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (sigma : Sigma) (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    fieldAction F b m hm heven Sigma hSigma sigma (quotientClass F b m hm heven X j) =
      quotientClass F b m hm heven (fieldSL F sigma X) j :=
  fieldQuotient_quotientClass F b m hm heven sigma _ X j

theorem fieldAction_specialInclusion (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (sigma : Sigma) (X : SpecialLinearGroup (Fin 2) F) :
    fieldAction F b m hm heven Sigma hSigma sigma (specialInclusion F b m hm heven X) =
      specialInclusion F b m hm heven (fieldSL F sigma X) := by
  rw [specialInclusion_apply, fieldAction_quotientClass, specialInclusion_apply]

theorem fieldAction_cyclicGenerator (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b)
    (sigma : Sigma) :
    fieldAction F b m hm heven Sigma hSigma sigma (cyclicGenerator F b m hm heven) =
      cyclicGenerator F b m hm heven := by
  rw [cyclicGenerator, fieldAction_quotientClass, map_one]

@[expose] def CyclicCentralSL2Data (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b) : Prop :=
  (nonsquareMatrix F b : Matrix (Fin 2) (Fin 2) F) = !![0, -(b : F); 1, 0] ∧
  (∀ X, SpecialLinearGroup.toGL (beta F b X) =
    nonsquareMatrix F b * SpecialLinearGroup.toGL X * (nonsquareMatrix F b)⁻¹) ∧
  beta F b ^ 2 = 1 ∧
  (∀ (X Y : SpecialLinearGroup (Fin 2) F) (j k : ZMod (2 * m)),
    pair F b m hm X j * pair F b m hm Y k =
      pair F b m hm (X * (beta F b ^ j.val) Y) (j + k)) ∧
  diagonalKernel F b m hm heven = Subgroup.zpowers (diagonalInvolution F b m hm) ∧
  diagonalKernel F b m hm heven ≤ Subgroup.center (PairGroup F b m hm) ∧
  Nat.card (diagonalKernel F b m hm heven) = 2 ∧
  (∀ X, specialInclusion F b m hm heven X = quotientClass F b m hm heven X 0) ∧
  cyclicGenerator F b m hm heven = quotientClass F b m hm heven 1 1 ∧
  (∀ (sigma : Sigma) (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)),
    fieldAction F b m hm heven Sigma hSigma sigma (quotientClass F b m hm heven X j) =
      quotientClass F b m hm heven (fieldSL F sigma X) j) ∧
  (∀ (sigma : Sigma) (X : SpecialLinearGroup (Fin 2) F) (i j : Fin 2),
    fieldSL F sigma X i j = (sigma : F ≃+* F) (X i j))

theorem cyclic_central_SL2_extension_data [Finite F]
    (_hodd : ringChar F ≠ 2) (b : Fˣ) (_hnonsquare : ¬ IsSquare b)
    (m : ℕ) (hm : 2 ≤ m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b) :
    CyclicCentralSL2Data F b m (by omega) heven Sigma hSigma := by
  exact ⟨nonsquareMatrix_val F b, beta_toGL F b, beta_square F b,
    pair_mul_explicit F b m _, rfl, diagonalKernel_le_center F b m _ heven,
    diagonalKernel_card F b m _ heven, specialInclusion_apply F b m _ heven,
    rfl, fieldAction_quotientClass F b m _ heven Sigma hSigma,
    fun sigma X i j => fieldSL_apply F sigma X i j⟩

abbrev SemilinearExtension (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ sigma ∈ Sigma, sigma (b : F) = b) :=
  CentralExtension F b m hm heven ⋊[fieldAction F b m hm heven Sigma hSigma] Sigma

end CFSG.Wreathed.CyclicCentralSL2Extension
