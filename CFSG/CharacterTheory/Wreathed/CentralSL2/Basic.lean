module

public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public section

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Algebra

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem cyclicAction_minusIdentity (j : Multiplicative (ZMod (2 * m))) :
    cyclicAction F b m hm j (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  change (beta F b ^ j.toAdd.val) _ = _
  induction j.toAdd.val with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, beta_minusIdentity]
    exact ih

theorem minusIdentity_mul (X : SpecialLinearGroup (Fin 2) F) :
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F * X = -X := by
  rw [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one, neg_one_mul]

theorem mul_minusIdentity (X : SpecialLinearGroup (Fin 2) F) :
    X * CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F = -X := by
  rw [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one, mul_neg_one]

theorem pair_mul_diagonalInvolution (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    pair F b m hm X j * diagonalInvolution F b m hm = pair F b m hm (-X) (j + m) := by
  rw [diagonalInvolution, pair_mul, cyclicAction_minusIdentity, mul_minusIdentity]

theorem pair_eq_iff (X Y : SpecialLinearGroup (Fin 2) F) (j k : ZMod (2 * m)) :
    pair F b m hm X j = pair F b m hm Y k ↔ X = Y ∧ j = k := by
  constructor
  · intro h
    have h1 := congrArg SemidirectProduct.left h
    have h2 := congrArg (fun g : PairGroup F b m hm => g.right.toAdd) h
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem quotientClass_eq_iff (X Y : SpecialLinearGroup (Fin 2) F) (j k : ZMod (2 * m)) :
    quotientClass F b m hm heven X j = quotientClass F b m hm heven Y k ↔
      (Y = X ∧ k = j) ∨ (Y = -X ∧ k = j + m) := by
  rw [quotientClass, quotientClass, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨d, hd, hdeq⟩
    rcases (CentralSL2Abelianization.mem_diagonal_iff heven).mp hd with rfl | rfl
    · left
      rw [mul_one, pair_eq_iff] at hdeq
      exact ⟨hdeq.1.symm, hdeq.2.symm⟩
    · right
      rw [pair_mul_diagonalInvolution, pair_eq_iff] at hdeq
      exact ⟨hdeq.1.symm, hdeq.2.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨1, Subgroup.one_mem _, mul_one _⟩
    · exact ⟨diagonalInvolution F b m hm, Subgroup.mem_zpowers _,
        pair_mul_diagonalInvolution F b m hm X j⟩

theorem quotientClass_neg (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    quotientClass F b m hm heven (-X) (j + m) = quotientClass F b m hm heven X j :=
  ((quotientClass_eq_iff F b m hm heven X (-X) j (j + m)).mpr (Or.inr ⟨rfl, rfl⟩)).symm

theorem quotientClass_mul (X Y : SpecialLinearGroup (Fin 2) F) (j k : ZMod (2 * m)) :
    quotientClass F b m hm heven X j * quotientClass F b m hm heven Y k =
      quotientClass F b m hm heven (X * (beta F b ^ j.val) Y) (j + k) := by
  rw [quotientClass, quotientClass, ← map_mul, pair_mul_explicit]
  rfl

theorem quotientClass_one :
    quotientClass F b m hm heven 1 0 = 1 := rfl

theorem quotientClass_surjective (g : CentralExtension F b m hm heven) :
    ∃ X j, quotientClass F b m hm heven X j = g := by
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (diagonalKernel F b m hm heven) g
  exact ⟨p.left, p.right.toAdd, rfl⟩

theorem beta_pow_one (n : ℕ) : (beta F b ^ n) (1 : SpecialLinearGroup (Fin 2) F) = 1 :=
  map_one _

theorem beta_pow_even (n : ℕ) (hn : Even n) (Y : SpecialLinearGroup (Fin 2) F) :
    (beta F b ^ n) Y = Y := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, beta_square, one_pow, MulAut.one_apply]

theorem beta_pow_odd (n : ℕ) (hn : Odd n) (Y : SpecialLinearGroup (Fin 2) F) :
    (beta F b ^ n) Y = beta F b Y := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, MulAut.mul_apply, beta_pow_even F b _ (even_two_mul k)]

theorem cyclicGenerator_pow (n : ℕ) :
    cyclicGenerator F b m hm heven ^ n = quotientClass F b m hm heven 1 n := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero]; rfl
  | succ n ih =>
    rw [pow_succ, ih, cyclicGenerator, quotientClass_mul, beta_pow_one, mul_one]
    push_cast
    rfl

theorem cyclicGenerator_pow_m :
    cyclicGenerator F b m hm heven ^ m =
      specialInclusion F b m hm heven (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) := by
  rw [cyclicGenerator_pow, specialInclusion_apply,
    CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one]
  have h := quotientClass_neg F b m hm heven (-1 : SpecialLinearGroup (Fin 2) F) 0
  rw [neg_neg, zero_add] at h
  exact h

theorem cyclicGenerator_sq_mem_center :
    cyclicGenerator F b m hm heven ^ 2 ∈ Subgroup.center (CentralExtension F b m hm heven) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨X, j, rfl⟩ := quotientClass_surjective F b m hm heven g
  rw [cyclicGenerator_pow, quotientClass_mul, quotientClass_mul, beta_pow_one, mul_one,
    beta_pow_even F b _ (by
      rw [ZMod.val_natCast]
      exact (Nat.even_iff.mpr (by
        have h2 : 2 % (2 * m) = 2 ∨ 2 % (2 * m) = 0 := by
          rcases Nat.lt_or_ge 2 (2 * m) with h | h
          · left; exact Nat.mod_eq_of_lt h
          · right
            have : 2 * m = 2 := by omega
            rw [this]
        rcases h2 with h2 | h2 <;> omega))), one_mul, add_comm]

theorem specialInclusion_mul_quotientClass (X Y : SpecialLinearGroup (Fin 2) F)
    (j : ZMod (2 * m)) :
    specialInclusion F b m hm heven X * quotientClass F b m hm heven Y j =
      quotientClass F b m hm heven (X * Y) j := by
  rw [specialInclusion_apply, quotientClass_mul, ZMod.val_zero, pow_zero, MulAut.one_apply,
    zero_add]

theorem quotientClass_eq_specialInclusion_mul (X : SpecialLinearGroup (Fin 2) F)
    (j : ZMod (2 * m)) :
    quotientClass F b m hm heven X j =
      specialInclusion F b m hm heven X * cyclicGenerator F b m hm heven ^ j.val := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [cyclicGenerator_pow, specialInclusion_mul_quotientClass, mul_one, ZMod.natCast_zmod_val]

end Algebra

theorem cast_val_eq {m : ℕ} (hm : 0 < m) (j : ZMod (2 * m)) :
    (ZMod.cast j : ZMod m) = (j.val : ZMod m) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [ZMod.cast_eq_val]

section Action

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

@[expose] noncomputable def coordJ : Equiv.Perm (Omega F) :=
  coordinateGLAction F (nonsquareMatrix F b)

theorem coordinateGLAction_scalar (c : Fˣ) :
    coordinateGLAction F (GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
  rw [coordinateGLAction, MonoidHom.comp_apply, ProjGenLinGroup.mk_scalar, map_one]

theorem coordJ_sq : coordJ F b ^ 2 = 1 := by
  rw [coordJ, ← map_pow, nonsquareMatrix_square, coordinateGLAction_scalar]

theorem coordJ_pow_two_mul (n : ℕ) : coordJ F b ^ (2 * n) = 1 := by
  rw [pow_mul, coordJ_sq, one_pow]

@[expose] noncomputable def cyclicPerm : Multiplicative (ZMod (2 * m)) →* Equiv.Perm (Omega F) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  refine {
    toFun := fun j => coordJ F b ^ j.toAdd.val
    map_one' := by simp
    map_mul' := ?_ }
  intro j k
  simp only [toAdd_mul, ZMod.val_add]
  rw [← pow_eq_pow_mod _ (coordJ_pow_two_mul F b m), pow_add]

theorem cyclicPerm_apply (j : Multiplicative (ZMod (2 * m))) :
    cyclicPerm F b m hm j = coordJ F b ^ j.toAdd.val := rfl

theorem toGL_beta_pow (n : ℕ) (X : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup.toGL ((beta F b ^ n) X) =
      nonsquareMatrix F b ^ n * SpecialLinearGroup.toGL X * (nonsquareMatrix F b ^ n)⁻¹ := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, beta_toGL, pow_succ]
    group

@[expose] noncomputable def pairAction : PairGroup F b m hm →* Equiv.Perm (Omega F) :=
  SemidirectProduct.lift ((coordinateGLAction F).comp SpecialLinearGroup.toGL)
    (cyclicPerm F b m hm) (by
      intro j
      refine MonoidHom.ext fun X => Equiv.ext fun x => ?_
      change coordinateGLAction F (SpecialLinearGroup.toGL ((beta F b ^ j.toAdd.val) X)) x =
        (coordJ F b ^ j.toAdd.val * coordinateGLAction F (SpecialLinearGroup.toGL X) *
          (coordJ F b ^ j.toAdd.val)⁻¹) x
      rw [toGL_beta_pow, map_mul, map_mul, map_inv, map_pow, coordJ])

theorem pairAction_pair (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    pairAction F b m hm (pair F b m hm X j) =
      coordinateGLAction F (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val) := by
  rw [map_mul, map_pow]
  rfl

theorem diagonalKernel_le_ker_pairAction :
    diagonalKernel F b m hm heven ≤ (pairAction F b m hm).ker := by
  rw [diagonalKernel, Subgroup.zpowers_le, MonoidHom.mem_ker, diagonalInvolution,
    pairAction_pair, ZMod.val_natCast_of_lt (by omega), map_mul, map_pow]
  obtain ⟨k, hk⟩ := heven
  have hneg : SpecialLinearGroup.toGL (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      GeneralLinearGroup.scalar (Fin 2) (-1) := by
    apply Units.ext
    change (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F : Matrix (Fin 2) (Fin 2) F) =
      Matrix.scalar (Fin 2) ((-1 : Fˣ) : F)
    rw [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix, Units.val_neg, Units.val_one]
  rw [hneg, coordinateGLAction_scalar, one_mul, hk, ← two_mul, ← coordJ, coordJ_pow_two_mul]

@[expose] noncomputable def projAction :
    CentralExtension F b m hm heven →* Equiv.Perm (Omega F) :=
  QuotientGroup.lift _ (pairAction F b m hm) (diagonalKernel_le_ker_pairAction F b m hm heven)

theorem projAction_quotientClass (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    projAction F b m hm heven (quotientClass F b m hm heven X j) =
      coordinateGLAction F (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val) :=
  pairAction_pair F b m hm X j

@[expose] noncomputable def fieldPerm : (F ≃+* F) →* Equiv.Perm (Omega F) where
  toFun σ := fieldExtension F σ
  map_one' := by
    ext x
    cases x <;> rfl
  map_mul' σ τ := by
    ext x
    cases x <;> rfl

theorem fieldPerm_apply (σ : F ≃+* F) : fieldPerm F σ = fieldExtension F σ := rfl

theorem fieldExtension_conj_coordinateGLAction (σ : F ≃+* F)
    (A : GeneralLinearGroup (Fin 2) F) :
    fieldExtension F σ * coordinateGLAction F A * (fieldExtension F σ)⁻¹ =
      coordinateGLAction F (GeneralLinearGroup.map σ.toRingHom A) := by
  refine Equiv.ext fun x => ?_
  have hσ : ∀ y : F, σ (σ.symm y) = y := σ.apply_symm_apply
  have hmap : ∀ i j, (GeneralLinearGroup.map σ.toRingHom A).val i j = σ (A.val i j) := by
    intro i j; rfl
  cases x with
  | none =>
    change fieldExtension F σ (coordinateGLAction F A ((fieldExtension F σ).symm none)) = _
    change fieldExtension F σ (coordinateGLAction F A none) = _
    by_cases hc : A.val 1 0 = 0
    · rw [coordinateGLAction_infinity_lower_left_zero F A hc,
        coordinateGLAction_infinity_lower_left_zero F _ (by rw [hmap, hc, map_zero])]
      rfl
    · rw [coordinateGLAction_infinity F A hc,
        coordinateGLAction_infinity F _ (by rw [hmap]; exact (map_ne_zero σ).mpr hc)]
      simp [map_div₀]
  | some y =>
    change fieldExtension F σ (coordinateGLAction F A (some (σ.symm y))) = _
    by_cases hd : A.val 1 0 * σ.symm y + A.val 1 1 = 0
    · rw [coordinateGLAction_finite_denominator_zero F A _ hd,
        coordinateGLAction_finite_denominator_zero F _ y (by
          rw [hmap, hmap, ← hσ y, ← map_mul, ← map_add, hd, map_zero])]
      rfl
    · have hd' : (GeneralLinearGroup.map σ.toRingHom A).val 1 0 * y +
          (GeneralLinearGroup.map σ.toRingHom A).val 1 1 ≠ 0 := by
        rw [hmap, hmap, ← hσ y, ← map_mul, ← map_add]
        exact (map_ne_zero σ).mpr hd
      rw [coordinateGLAction_finite F A _ hd, coordinateGLAction_finite F _ y hd']
      simp only [fieldExtension_some, hmap, map_div₀, map_add, map_mul, hσ]

theorem map_nonsquareMatrix_pow (σ : F ≃+* F) (hb : σ (b : F) = b) (n : ℕ) :
    GeneralLinearGroup.map σ.toRingHom (nonsquareMatrix F b ^ n) = nonsquareMatrix F b ^ n := by
  rw [map_pow, field_map_nonsquareMatrix F b σ hb]

variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem projAction_fieldAction (σ : Sigma) (g : CentralExtension F b m hm heven) :
    projAction F b m hm heven (fieldAction F b m hm heven Sigma hSigma σ g) =
      fieldPerm F σ * projAction F b m hm heven g * (fieldPerm F σ)⁻¹ := by
  obtain ⟨X, j, rfl⟩ := quotientClass_surjective F b m hm heven g
  rw [fieldAction_quotientClass, projAction_quotientClass, projAction_quotientClass,
    fieldPerm_apply, fieldExtension_conj_coordinateGLAction]
  congr 1
  rw [map_mul (GeneralLinearGroup.map _), map_nonsquareMatrix_pow F b σ (hSigma σ σ.2),
    fieldSL_toGL]

@[expose] noncomputable def semilinearAction :
    SemilinearExtension F b m hm heven Sigma hSigma →* Equiv.Perm (Omega F) :=
  SemidirectProduct.lift (projAction F b m hm heven) ((fieldPerm F).comp Sigma.subtype) (by
    intro σ
    refine MonoidHom.ext fun g => Equiv.ext fun x => ?_
    change projAction F b m hm heven (fieldAction F b m hm heven Sigma hSigma σ g) x =
      (fieldPerm F σ * projAction F b m hm heven g * (fieldPerm F σ)⁻¹) x
    rw [projAction_fieldAction])

theorem semilinearAction_mk (g : CentralExtension F b m hm heven) (σ : Sigma) :
    semilinearAction F b m hm heven Sigma hSigma ⟨g, σ⟩ =
      projAction F b m hm heven g * fieldExtension F σ := rfl

theorem semilinearAction_inl (g : CentralExtension F b m hm heven) :
    semilinearAction F b m hm heven Sigma hSigma (SemidirectProduct.inl g) =
      projAction F b m hm heven g := by
  rw [semilinearAction, SemidirectProduct.lift_inl]

end Action


section Matrices

variable (F : Type) [Field F]

@[expose] def upperSL (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [det_fin_two]⟩

@[expose] def lowerSL (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [det_fin_two]⟩

@[expose] def diagSL (c : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [det_fin_two]⟩

theorem upperSL_val (t : F) : (upperSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem lowerSL_val (t : F) : (lowerSL F t : Matrix (Fin 2) (Fin 2) F) = !![1, 0; t, 1] := rfl

theorem diagSL_val (c : Fˣ) :
    (diagSL F c : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] := rfl

theorem upperSL_add (s t : F) : upperSL F (s + t) = upperSL F s * upperSL F t := by
  apply Subtype.ext
  change !![1, s + t; 0, 1] = !![1, s; 0, 1] * !![(1 : F), t; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem lowerSL_add (s t : F) : lowerSL F (s + t) = lowerSL F s * lowerSL F t := by
  apply Subtype.ext
  change !![1, 0; s + t, 1] = !![1, 0; s, 1] * !![(1 : F), 0; t, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem upperSL_zero : upperSL F 0 = 1 := by
  apply Subtype.ext
  change !![(1 : F), 0; 0, 1] = 1
  rw [Matrix.one_fin_two]

theorem lowerSL_zero : lowerSL F 0 = 1 := by
  apply Subtype.ext
  change !![(1 : F), 0; 0, 1] = 1
  rw [Matrix.one_fin_two]

theorem diagSL_mul (c d : Fˣ) : diagSL F (c * d) = diagSL F c * diagSL F d := by
  apply Subtype.ext
  change !![((c * d : Fˣ) : F), 0; 0, (((c * d)⁻¹ : Fˣ) : F)] =
    !![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] * !![(d : F), 0; 0, ((d⁻¹ : Fˣ) : F)]
  rw [Matrix.mul_fin_two]
  simp [mul_comm]

theorem diagSL_one : diagSL F 1 = 1 := by
  apply Subtype.ext
  change !![((1 : Fˣ) : F), 0; 0, (((1 : Fˣ)⁻¹ : Fˣ) : F)] = 1
  rw [Matrix.one_fin_two]
  simp

@[expose] def upperHom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun t := upperSL F t.toAdd
  map_one' := upperSL_zero F
  map_mul' s t := upperSL_add F s.toAdd t.toAdd

@[expose] def lowerHom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun t := lowerSL F t.toAdd
  map_one' := lowerSL_zero F
  map_mul' s t := lowerSL_add F s.toAdd t.toAdd

@[expose] def diagHom : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun := diagSL F
  map_one' := diagSL_one F
  map_mul' := diagSL_mul F

theorem upperSL_neg_eq_inv (t : F) : upperSL F (-t) = (upperSL F t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← upperSL_add, neg_add_cancel, upperSL_zero]

theorem lowerSL_neg_eq_inv (t : F) : lowerSL F (-t) = (lowerSL F t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← lowerSL_add, neg_add_cancel, lowerSL_zero]

theorem upperSL_eq_transvection (t : F) :
    upperSL F t = SpecialLinearGroup.transvection zero_ne_one t := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, upperSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lowerSL_eq_transvection (t : F) :
    lowerSL F t = SpecialLinearGroup.transvection one_ne_zero t := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, lowerSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weyl_val :
    (CentralSL2Abelianization.weyl F : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := rfl

variable (b : Fˣ)

theorem nonsquareMatrix_inv_val :
    (((nonsquareMatrix F b)⁻¹ : GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; -((b : F)⁻¹), 0] := by
  have hb : (b : F) ≠ 0 := b.ne_zero
  have hmul : (nonsquareMatrix F b : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -((b : F)⁻¹), 0] = 1 := by
    rw [nonsquareMatrix_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hb]
  have h := Matrix.inv_eq_right_inv hmul
  rw [Matrix.coe_units_inv, h]

theorem beta_val (X : SpecialLinearGroup (Fin 2) F) :
    (beta F b X : Matrix (Fin 2) (Fin 2) F) =
      !![X 1 1, -(b : F) * X 1 0; -(X 0 1) / b, X 0 0] := by
  have h := congrArg (fun A : GeneralLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F))
    (beta_toGL F b X)
  change (beta F b X : Matrix (Fin 2) (Fin 2) F) =
      (nonsquareMatrix F b : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) *
        (((nonsquareMatrix F b)⁻¹ : GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    at h
  rw [h, nonsquareMatrix_inv_val, nonsquareMatrix_val,
    Matrix.eta_fin_two (X : Matrix (Fin 2) (Fin 2) F), Matrix.mul_fin_two, Matrix.mul_fin_two]
  have hb : (b : F) ≠ 0 := b.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

end Matrices

section Instances

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

instance pairGroup_finite : Finite (PairGroup F b m hm) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  exact Finite.of_equiv _ (SemidirectProduct.equivProd (N := SpecialLinearGroup (Fin 2) F)
    (G := Multiplicative (ZMod (2 * m))) (φ := cyclicAction F b m hm)).symm

noncomputable instance centralExtension_fintype : Fintype (CentralExtension F b m hm heven) :=
  Fintype.ofFinite _

variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

instance semilinearExtension_finite :
    Finite (SemilinearExtension F b m hm heven Sigma hSigma) := by
  have : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  exact Finite.of_equiv _ (SemidirectProduct.equivProd
    (N := CentralExtension F b m hm heven) (G := Sigma)
    (φ := fieldAction F b m hm heven Sigma hSigma)).symm

noncomputable instance semilinearExtension_fintype :
    Fintype (SemilinearExtension F b m hm heven Sigma hSigma) :=
  Fintype.ofFinite _

end Instances

section ActionInstances

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

noncomputable instance centralExtension_mulAction :
    MulAction (CentralExtension F b m hm heven) (Omega F) :=
  MulAction.compHom _ (projAction F b m hm heven)

theorem centralExtension_smul_def (g : CentralExtension F b m hm heven) (x : Omega F) :
    g • x = projAction F b m hm heven g x := rfl

variable (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

noncomputable instance semilinearExtension_mulAction :
    MulAction (SemilinearExtension F b m hm heven Sigma hSigma) (Omega F) :=
  MulAction.compHom _ (semilinearAction F b m hm heven Sigma hSigma)

theorem semilinearExtension_smul_def (h : SemilinearExtension F b m hm heven Sigma hSigma)
    (x : Omega F) : h • x = semilinearAction F b m hm heven Sigma hSigma h x := rfl

end ActionInstances

section Cardinality

variable (F : Type) [Field F] [Finite F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

omit [Finite F] in
theorem card_pairGroup :
    Nat.card (PairGroup F b m hm) = Nat.card (SpecialLinearGroup (Fin 2) F) * (2 * m) := by
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [SemidirectProduct.card, Nat.card_eq_fintype_card (α := Multiplicative (ZMod (2 * m))),
    Fintype.card_multiplicative, ZMod.card]

omit [Finite F] in
theorem card_centralExtension :
    Nat.card (CentralExtension F b m hm heven) = m * Nat.card (SpecialLinearGroup (Fin 2) F) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (diagonalKernel F b m hm heven)
  rw [diagonalKernel_card, card_pairGroup] at h
  have : Nat.card (CentralExtension F b m hm heven) * 2 =
      (m * Nat.card (SpecialLinearGroup (Fin 2) F)) * 2 := by
    rw [← h]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) this

theorem card_SL_two :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [Nat.card_eq_fintype_card]
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hq2 : Fintype.card F - 1 ≠ 0 := by
    have : 2 ≤ Fintype.card F := by
      have := Fintype.one_lt_card (α := F)
      omega
    omega
  have hfac : (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) =
      Fintype.card F * (Fintype.card F ^ 2 - 1) * (Fintype.card F - 1) := by
    have : Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) := by
      rw [Nat.mul_sub, mul_one, sq]
    rw [this]
    ring
  rw [hfac, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hq2)]

end Cardinality

end CFSG.Wreathed.CentralSL2
