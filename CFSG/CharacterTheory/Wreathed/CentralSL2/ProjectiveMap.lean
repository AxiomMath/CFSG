module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseBorel

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section ProjectiveMap

variable (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)

theorem mk_nonsquareMatrix_sq :
    (ProjGenLinGroup.mk (nonsquareMatrix F b) : ProjGenLinGroup (Fin 2) F) ^ 2 = 1 := by
  rw [← map_pow, nonsquareMatrix_square, ProjGenLinGroup.mk_scalar]

theorem mk_nonsquareMatrix_pow_two_mul (n : ℕ) :
    (ProjGenLinGroup.mk (nonsquareMatrix F b) : ProjGenLinGroup (Fin 2) F) ^ (2 * n) = 1 := by
  rw [pow_mul, mk_nonsquareMatrix_sq, one_pow]

@[expose] noncomputable def cyclicPGL :
    Multiplicative (ZMod (2 * m)) →* ProjGenLinGroup (Fin 2) F := by
  let : NeZero (2 * m) := ⟨by omega⟩
  refine {
    toFun := fun j => ProjGenLinGroup.mk (nonsquareMatrix F b) ^ j.toAdd.val
    map_one' := by simp
    map_mul' := ?_ }
  intro j k
  simp only [toAdd_mul, ZMod.val_add]
  rw [← pow_eq_pow_mod _ (mk_nonsquareMatrix_pow_two_mul F b m), pow_add]

@[expose] noncomputable def pairPGL : PairGroup F b m hm →* ProjGenLinGroup (Fin 2) F :=
  SemidirectProduct.lift (ProjGenLinGroup.mk.comp SpecialLinearGroup.toGL)
    (cyclicPGL F b m hm) (by
      intro j
      refine MonoidHom.ext fun X => ?_
      change ProjGenLinGroup.mk (SpecialLinearGroup.toGL ((beta F b ^ j.toAdd.val) X)) =
        ProjGenLinGroup.mk (nonsquareMatrix F b) ^ j.toAdd.val *
          ProjGenLinGroup.mk (SpecialLinearGroup.toGL X) *
            (ProjGenLinGroup.mk (nonsquareMatrix F b) ^ j.toAdd.val)⁻¹
      rw [toGL_beta_pow, map_mul, map_mul, map_inv, map_pow])

theorem pairPGL_pair (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    pairPGL F b m hm (pair F b m hm X j) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val) := by
  rw [map_mul, map_pow]
  rfl

theorem toGL_minusIdentity :
    SpecialLinearGroup.toGL (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) =
      GeneralLinearGroup.scalar (Fin 2) (-1) := by
  apply Units.ext
  change (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F : Matrix (Fin 2) (Fin 2) F) =
    Matrix.scalar (Fin 2) ((-1 : Fˣ) : F)
  rw [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix, Units.val_neg, Units.val_one]

theorem diagonalKernel_le_ker_pairPGL :
    diagonalKernel F b m hm heven ≤ (pairPGL F b m hm).ker := by
  rw [diagonalKernel, Subgroup.zpowers_le, MonoidHom.mem_ker, diagonalInvolution,
    pairPGL_pair, ZMod.val_natCast_of_lt (by omega), map_mul, map_pow, toGL_minusIdentity,
    ProjGenLinGroup.mk_scalar, one_mul]
  obtain ⟨k, hk⟩ := heven
  rw [hk, ← two_mul, mk_nonsquareMatrix_pow_two_mul]

@[expose] noncomputable def projectiveMap :
    CentralExtension F b m hm heven →* ProjGenLinGroup (Fin 2) F :=
  QuotientGroup.lift _ (pairPGL F b m hm) (diagonalKernel_le_ker_pairPGL F b m hm heven)

theorem projectiveMap_quotientClass (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) :
    projectiveMap F b m hm heven (quotientClass F b m hm heven X j) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val) :=
  pairPGL_pair F b m hm X j

theorem projectiveMap_specialInclusion (X : SpecialLinearGroup (Fin 2) F) :
    projectiveMap F b m hm heven (specialInclusion F b m hm heven X) =
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL X) := by
  rw [specialInclusion_apply, projectiveMap_quotientClass, ZMod.val_zero, pow_zero, mul_one]

theorem projectiveMap_cyclicGenerator :
    projectiveMap F b m hm heven (cyclicGenerator F b m hm heven) =
      ProjGenLinGroup.mk (nonsquareMatrix F b) := by
  rw [cyclicGenerator, projectiveMap_quotientClass, one_val_eq_one, pow_one, map_one, one_mul]

theorem coordinatePGLAction_projectiveMap (g : CentralExtension F b m hm heven) :
    coordinatePGLAction F (projectiveMap F b m hm heven g) = projAction F b m hm heven g := by
  obtain ⟨X, j, rfl⟩ := quotientClass_surjective F b m hm heven g
  rw [projectiveMap_quotientClass, projAction_quotientClass]
  rfl

theorem projectiveMap_ker (hb : ¬ IsSquare b) :
    (projectiveMap F b m hm heven).ker =
      Subgroup.zpowers (cyclicGenerator F b m hm heven ^ 2) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    rw [← fixes_all_iff F b m hm heven hb]
    intro x
    rw [centralExtension_smul_def, ← coordinatePGLAction_projectiveMap, hg, map_one]
    rfl
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [map_zpow, map_pow, projectiveMap_cyclicGenerator, mk_nonsquareMatrix_sq, _root_.one_zpow]

theorem isSquare_mul_inv_of_not_isSquare [Finite F] {d e : Fˣ} (hd : ¬ IsSquare d)
    (he : ¬ IsSquare e) : IsSquare (d * e⁻¹) := by
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hodd : ∀ x : Fˣ, ¬ IsSquare x → ∃ i : ℤ, Odd i ∧ g₀ ^ i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ x)
    refine ⟨i, ?_, hi⟩
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨j, hj⟩ := hev
    exact hx ⟨g₀ ^ j, by rw [← hi, hj, _root_.zpow_add]⟩
  obtain ⟨i, hi, rfl⟩ := hodd d hd
  obtain ⟨k, hk, rfl⟩ := hodd e he
  obtain ⟨j, hj⟩ := Int.even_sub.mpr
    (iff_of_false (Int.not_even_iff_odd.mpr hi) (Int.not_even_iff_odd.mpr hk))
  refine ⟨g₀ ^ j, ?_⟩
  rw [← _root_.zpow_neg, ← _root_.zpow_add, ← _root_.zpow_add, ← sub_eq_add_neg, hj]

theorem projectiveMap_surjective [Finite F] (hb : ¬ IsSquare b) :
    Function.Surjective (projectiveMap F b m hm heven) := by
  intro P
  obtain ⟨M, rfl⟩ := ProjGenLinGroup.mk_surjective P
  have hsq : ∀ d : Fˣ, IsSquare d → ∃ c : Fˣ, c ^ 2 * d = 1 := by
    rintro d ⟨s, rfl⟩
    exact ⟨s⁻¹, by group⟩
  have hscal : ∀ (c : Fˣ) (N : Matrix (Fin 2) (Fin 2) F),
      (c : F) • N * Matrix.scalar (Fin 2) ((c⁻¹ : Fˣ) : F) = N := by
    intro c N
    have hc : (c : F) ≠ 0 := c.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] <;>
      field_simp
  by_cases hdet : IsSquare (GeneralLinearGroup.det M)
  · obtain ⟨c, hc⟩ := hsq _ hdet
    let X : SpecialLinearGroup (Fin 2) F :=
      ⟨(c : F) • (M : Matrix (Fin 2) (Fin 2) F), by
        rw [Matrix.det_smul, Fintype.card_fin]
        have h := congrArg Units.val hc
        simpa using h⟩
    refine ⟨specialInclusion F b m hm heven X, ?_⟩
    rw [projectiveMap_specialInclusion, ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨c⁻¹, Units.ext ?_⟩
    exact hscal c M
  · have hd : IsSquare (GeneralLinearGroup.det M * b⁻¹) :=
      isSquare_mul_inv_of_not_isSquare F hdet hb
    obtain ⟨c, hc⟩ := hsq _ hd
    let X : SpecialLinearGroup (Fin 2) F :=
      ⟨(c : F) • (M : Matrix (Fin 2) (Fin 2) F) *
          (((nonsquareMatrix F b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
        rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin]
        have h := congrArg Units.val hc
        have hdetJ : GeneralLinearGroup.det (nonsquareMatrix F b) = b := by
          apply Units.ext
          rw [GeneralLinearGroup.val_det_apply, nonsquareMatrix_val, Matrix.det_fin_two_of]
          ring
        have hJ : (((nonsquareMatrix F b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
            ((b⁻¹ : Fˣ) : F) := by
          rw [← GeneralLinearGroup.val_det_apply, map_inv, hdetJ]
        rw [hJ]
        simpa [mul_assoc] using h⟩
    refine ⟨quotientClass F b m hm heven X 1, ?_⟩
    rw [projectiveMap_quotientClass, one_val_eq_one, pow_one, ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨c⁻¹, Units.ext ?_⟩
    change (c : F) • (M : Matrix (Fin 2) (Fin 2) F) *
        (((nonsquareMatrix F b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (nonsquareMatrix F b : Matrix (Fin 2) (Fin 2) F) *
            Matrix.scalar (Fin 2) ((c⁻¹ : Fˣ) : F) = M
    rw [mul_assoc ((c : F) • (M : Matrix (Fin 2) (Fin 2) F)), Units.inv_mul, mul_one]
    exact hscal c M

end ProjectiveMap

end CFSG.Wreathed.CentralSL2
