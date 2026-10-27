module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ProjectiveLine
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Orders

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem one_ne_neg_one_SL (h2 : (2 : F) ≠ 0) : (1 : SpecialLinearGroup (Fin 2) F) ≠ -1 := by
  intro h
  have h00 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X.val 0 0) h
  change (1 : Matrix (Fin 2) (Fin 2) F) 0 0 = (-(1 : Matrix (Fin 2) (Fin 2) F)) 0 0 at h00
  rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  apply h2
  linear_combination h00

theorem cyclicGenerator_pow_eq_one_iff (h2 : (2 : F) ≠ 0) (n : ℕ) :
    cyclicGenerator F b m hm heven ^ n = 1 ↔ 2 * m ∣ n := by
  rw [cyclicGenerator_pow, ← quotientClass_one, quotientClass_eq_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact (ZMod.natCast_eq_zero_iff n (2 * m)).mp h.symm
    · exact absurd h (one_ne_neg_one_SL F h2)
  · intro h
    left
    exact ⟨rfl, ((ZMod.natCast_eq_zero_iff n (2 * m)).mpr h).symm⟩

theorem orderOf_cyclicGenerator (h2 : (2 : F) ≠ 0) :
    orderOf (cyclicGenerator F b m hm heven) = 2 * m := by
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((cyclicGenerator_pow_eq_one_iff F b m hm heven h2 _).mpr
      dvd_rfl)
  · exact (cyclicGenerator_pow_eq_one_iff F b m hm heven h2 _).mp (pow_orderOf_eq_one _)

theorem orderOf_cyclicGenerator_sq (h2 : (2 : F) ≠ 0) :
    orderOf (cyclicGenerator F b m hm heven ^ 2) = m := by
  have hdvd : 2 ∣ orderOf (cyclicGenerator F b m hm heven) := by
    rw [orderOf_cyclicGenerator F b m hm heven h2]
    exact dvd_mul_right 2 m
  rw [orderOf_pow_of_dvd two_ne_zero hdvd, orderOf_cyclicGenerator F b m hm heven h2,
    Nat.mul_div_cancel_left m two_pos]

end Orders

section Kernel

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem projAction_cyclicGenerator :
    projAction F b m hm heven (cyclicGenerator F b m hm heven) = coordJ F b := by
  rw [cyclicGenerator, projAction_quotientClass, ZMod.val_one'' (by omega), pow_one, map_one,
    one_mul]
  rfl

theorem projAction_cyclicGenerator_sq :
    projAction F b m hm heven (cyclicGenerator F b m hm heven ^ 2) = 1 := by
  rw [map_pow, projAction_cyclicGenerator, coordJ_sq]

theorem fieldExtension_eq_one_iff (σ : F ≃+* F) : fieldExtension F σ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    ext x
    have hx := congrArg (fun f : Equiv.Perm (Omega F) => f (some x)) h
    simpa using hx
  · rintro rfl
    refine Equiv.ext fun x => ?_
    cases x <;> rfl

theorem semilinearAction_ker (hb : ¬ IsSquare b) :
    (semilinearAction F b m hm heven Sigma hSigma).ker =
      Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2)) := by
  apply le_antisymm
  · rintro ⟨g, σ⟩ hgσ
    obtain ⟨X, j, rfl⟩ := quotientClass_surjective F b m hm heven g
    rw [MonoidHom.mem_ker, semilinearAction_mk, projAction_quotientClass] at hgσ
    set C := SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val with hC
    have hfix : ∀ x, coordinateGLAction F C (fieldExtension F σ x) = x := fun x => by
      have := congrArg (fun f : Equiv.Perm (Omega F) => f x) hgσ
      simpa using this
    have h10 : C.val 1 0 = 0 := (coordinateGLAction_none_eq_none_iff C).mp (hfix none)
    have h01 : C.val 0 1 = 0 := by
      have h := hfix (some 0)
      rw [fieldExtension_some, map_zero, coordinateGLAction_some_eq_some_iff] at h
      linear_combination -h
    have h11 : C.val 1 1 = C.val 0 0 := by
      have h := hfix (some 1)
      rw [fieldExtension_some, map_one, coordinateGLAction_some_eq_some_iff, h10, h01] at h
      linear_combination h
    have h00 : C.val 0 0 ≠ 0 := by
      intro h00
      have hdet := C.det_ne_zero
      rw [det_fin_two, h10, h00] at hdet
      simp at hdet
    have hscalar : C = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (C.val 0 0) h00) := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [h10, h01, h11]
    have hσ : σ = 1 := by
      apply Subtype.ext
      apply (fieldExtension_eq_one_iff F σ).mp
      refine Equiv.ext fun x => ?_
      have := hfix x
      rw [hscalar, coordinateGLAction_scalar, Equiv.Perm.one_apply] at this
      rw [Equiv.Perm.one_apply]
      exact this
    subst hσ
    have hdetC : C.det = b ^ j.val := by
      rw [hC, map_mul, map_pow]
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply]
      rw [show (SpecialLinearGroup.toGL X : Matrix (Fin 2) (Fin 2) F) = (X : Matrix _ _ F) from
        rfl, X.2, nonsquareMatrix_val, det_fin_two_of]
      simp
    have hjeven : Even j.val := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨k, hk⟩ := hodd
      apply hb
      have hd := congrArg (fun A : GeneralLinearGroup (Fin 2) F => GeneralLinearGroup.det A) hscalar
      rw [hdetC, GeneralLinearGroup.det_scalar, Fintype.card_fin, hk] at hd
      have hdF := congrArg Units.val hd
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at hdF
      have hbk : (b : F) ^ k ≠ 0 := pow_ne_zero k b.ne_zero
      have hr : C.val 0 0 / (b : F) ^ k ≠ 0 := div_ne_zero h00 hbk
      refine ⟨Units.mk0 (C.val 0 0 / (b : F) ^ k) hr * 1, ?_⟩
      apply Units.ext
      simp only [mul_one, Units.val_mul, Units.val_mk0]
      field_simp
      linear_combination hdF
    obtain ⟨k, hk⟩ := hjeven
    have hJ : nonsquareMatrix F b ^ j.val = GeneralLinearGroup.scalar (Fin 2) ((-b) ^ k) := by
      rw [hk, ← two_mul, pow_mul, nonsquareMatrix_square, map_pow]
    have hXc : SpecialLinearGroup.toGL X =
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (C.val 0 0) h00 * ((-b) ^ k)⁻¹) := by
      rw [map_mul, map_inv, ← hJ, ← hscalar, hC, mul_inv_cancel_right]
    have hXcenter : X ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
      rw [← SpecialLinearGroup.toGL_mem_center_iff, hXc, GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have : NeZero (2 * m) := ⟨by omega⟩
    have hj : j = ((2 * k : ℕ) : ZMod (2 * m)) := by
      rw [← ZMod.natCast_zmod_val j, hk]
      congr 1
      ring
    rcases (CFSG.Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F X).mp
      hXcenter with rfl | rfl
    · refine ⟨k, ?_⟩
      change (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
        SemilinearExtension F b m hm heven Sigma hSigma) ^ (k : ℤ) =
          SemidirectProduct.inl (quotientClass F b m hm heven 1 j)
      rw [zpow_natCast, ← map_pow, ← pow_mul, cyclicGenerator_pow, hj]
    · obtain ⟨l, hl⟩ := id heven
      refine ⟨k + l, ?_⟩
      change (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
        SemilinearExtension F b m hm heven Sigma hSigma) ^ ((k + l : ℕ) : ℤ) =
          SemidirectProduct.inl (quotientClass F b m hm heven
            (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) j)
      rw [zpow_natCast, ← map_pow, ← pow_mul, cyclicGenerator_pow,
        CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one]
      have h := quotientClass_neg F b m hm heven (1 : SpecialLinearGroup (Fin 2) F)
        ((2 * (k + l) : ℕ) : ZMod (2 * m))
      have hjm : j = ((2 * (k + l) : ℕ) : ZMod (2 * m)) + (m : ZMod (2 * m)) := by
        rw [hj]
        have h0 : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
        have hml := congrArg (fun n : ℕ => (n : ZMod (2 * m))) hl
        push_cast at h0 hml ⊢
        linear_combination hml - h0
      rw [hjm, h]
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, semilinearAction_inl,
      projAction_cyclicGenerator_sq]

theorem card_zpowers_inl_sq (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.zpowers (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ 2) :
      SemilinearExtension F b m hm heven Sigma hSigma)) = m := by
  rw [Nat.card_zpowers, orderOf_injective _ SemidirectProduct.inl_injective,
    orderOf_cyclicGenerator_sq F b m hm heven h2]

end Kernel

section Transitivity

variable (F : Type) [Field F]

theorem coordinateGLAction_toGL_none (X : SpecialLinearGroup (Fin 2) F) :
    coordinateGLAction F (SpecialLinearGroup.toGL X) none =
      if X 1 0 = 0 then none else some (X 0 0 / X 1 0) := by
  split_ifs with h
  · exact coordinateGLAction_infinity_lower_left_zero F _ h
  · exact coordinateGLAction_infinity F _ h

theorem coordinateGLAction_toGL_zero (X : SpecialLinearGroup (Fin 2) F) :
    coordinateGLAction F (SpecialLinearGroup.toGL X) (some 0) =
      if X 1 1 = 0 then none else some (X 0 1 / X 1 1) := by
  split_ifs with h
  · exact coordinateGLAction_finite_denominator_zero F _ 0 (by
      change X 1 0 * 0 + X 1 1 = 0
      rw [h, mul_zero, add_zero])
  · rw [coordinateGLAction_finite F _ 0 (by
      change X 1 0 * 0 + X 1 1 ≠ 0
      rwa [mul_zero, zero_add])]
    change some ((X 0 0 * 0 + X 0 1) / (X 1 0 * 0 + X 1 1)) = _
    rw [mul_zero, mul_zero, zero_add, zero_add]

@[expose] def pointToInfinity (x : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![x, -1; 1, 0], by simp [det_fin_two]⟩

@[expose] noncomputable def pointsToPoints (x y : F) (h : x - y ≠ 0) :
    SpecialLinearGroup (Fin 2) F :=
  ⟨!![x, y / (x - y); 1, 1 / (x - y)], by rw [det_fin_two_of]; field_simp⟩

theorem exists_SL_infinity_zero (c d : Omega F) (hcd : c ≠ d) :
    ∃ X : SpecialLinearGroup (Fin 2) F,
      coordinateGLAction F (SpecialLinearGroup.toGL X) none = c ∧
        coordinateGLAction F (SpecialLinearGroup.toGL X) (some 0) = d := by
  cases c with
  | none =>
    cases d with
    | none => exact absurd rfl hcd
    | some y =>
      refine ⟨upperSL F y, ?_, ?_⟩
      · rw [coordinateGLAction_toGL_none]
        simp [upperSL]
      · rw [coordinateGLAction_toGL_zero]
        simp [upperSL]
  | some x =>
    cases d with
    | none =>
      refine ⟨pointToInfinity F x, ?_, ?_⟩
      · rw [coordinateGLAction_toGL_none]
        simp [pointToInfinity]
      · rw [coordinateGLAction_toGL_zero]
        simp [pointToInfinity]
    | some y =>
      have hxy : x - y ≠ 0 := by
        intro h
        apply hcd
        rw [sub_eq_zero.mp h]
      refine ⟨pointsToPoints F x y hxy, ?_, ?_⟩
      · rw [coordinateGLAction_toGL_none]
        simp [pointsToPoints]
      · rw [coordinateGLAction_toGL_zero]
        have h1 : (pointsToPoints F x y hxy : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 / (x - y) := rfl
        have h0 : (pointsToPoints F x y hxy : Matrix (Fin 2) (Fin 2) F) 0 1 = y / (x - y) := rfl
        have hne : (1 : F) / (x - y) ≠ 0 := one_div_ne_zero hxy
        rw [ite_eq_right fun h => hne (h1 ▸ h), h0, h1]
        congr 1
        field_simp

variable (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem semilinearAction_matrixInclusion (X : SpecialLinearGroup (Fin 2) F) :
    semilinearAction F b m hm heven Sigma hSigma (matrixInclusion F b m hm heven Sigma hSigma X) =
      coordinateGLAction F (SpecialLinearGroup.toGL X) := by
  change semilinearAction F b m hm heven Sigma hSigma
    (SemidirectProduct.inl (specialInclusion F b m hm heven X)) = _
  rw [semilinearAction_inl, specialInclusion_apply, projAction_quotientClass, ZMod.val_zero,
    pow_zero, mul_one]

theorem matrixLayer_isMultiplyPretransitive :
    MulAction.IsMultiplyPretransitive (matrixLayer F b m hm heven Sigma hSigma) (Omega F) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a a' c d haa' hcd
  obtain ⟨Y, hY1, hY2⟩ := exists_SL_infinity_zero F a a' haa'
  obtain ⟨X, hX1, hX2⟩ := exists_SL_infinity_zero F c d hcd
  let g : matrixLayer F b m hm heven Sigma hSigma :=
    ⟨matrixInclusion F b m hm heven Sigma hSigma (X * Y⁻¹), MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  refine ⟨g, ?_, ?_⟩
  · rw [Subgroup.smul_def, semilinearExtension_smul_def, semilinearAction_matrixInclusion,
      map_mul, map_mul, map_inv, map_inv, Equiv.Perm.mul_apply,
      (Equiv.Perm.inv_eq_iff_eq.mpr hY1.symm), hX1]
  · rw [Subgroup.smul_def, semilinearExtension_smul_def, semilinearAction_matrixInclusion,
      map_mul, map_mul, map_inv, map_inv, Equiv.Perm.mul_apply,
      (Equiv.Perm.inv_eq_iff_eq.mpr hY2.symm), hX2]

theorem semilinearExtension_isMultiplyPretransitive :
    MulAction.IsMultiplyPretransitive (SemilinearExtension F b m hm heven Sigma hSigma)
      (Omega F) 2 := by
  have hM := matrixLayer_isMultiplyPretransitive F b m hm heven Sigma hSigma
  rw [MulAction.is_two_pretransitive_iff] at hM ⊢
  intro a a' c d haa' hcd
  obtain ⟨g, hg1, hg2⟩ := hM haa' hcd
  exact ⟨g, hg1, hg2⟩

end Transitivity

end CFSG.Wreathed.CentralSL2
