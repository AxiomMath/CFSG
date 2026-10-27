module

public import CFSG.ClassicalInvolution.AschTight.S19KLinStd

public section

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

@[expose] noncomputable def gam (F : Type) [Field F] : MulAut SL(3, F) where
  toFun x := (x⁻¹).transpose
  invFun x := (x⁻¹).transpose
  left_inv x := by
    apply Subtype.ext
    show (adjugate (adjugate x.1)ᵀ)ᵀ = x.1
    rw [Matrix.adjugate_transpose, Matrix.transpose_transpose,
      Matrix.adjugate_adjugate _ (by simp)]
    simp [x.2]
  right_inv x := by
    apply Subtype.ext
    show (adjugate (adjugate x.1)ᵀ)ᵀ = x.1
    rw [Matrix.adjugate_transpose, Matrix.transpose_transpose,
      Matrix.adjugate_adjugate _ (by simp)]
    simp [x.2]
  map_mul' x y := by
    apply Subtype.ext
    show (adjugate (x.1 * y.1))ᵀ = (adjugate x.1)ᵀ * (adjugate y.1)ᵀ
    rw [Matrix.adjugate_mul_distrib, Matrix.transpose_mul]

variable {F : Type} [Field F]

theorem gam_gam (x : SL(3, F)) : gam F (gam F x) = x := (gam F).left_inv x

@[expose] def J2 : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem J2_mul_J2 : (J2 : SL(2, F)) * J2 = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def J3 (F : Type) [Field F] : SL(3, F) :=
  blockSL F 3 2 0 (by omega) J2

theorem coe_J3 : ((J3 F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [J3, coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2]

theorem J3_mul_J3 : J3 F * J3 F = blockSL F 3 2 0 (by omega) (-1) := by
  rw [J3, ← map_mul, J2_mul_J2]

theorem gam_J3 : gam F (J3 F) = J3 F := by
  apply Subtype.ext
  show (adjugate (J3 F).1)ᵀ = (J3 F).1
  rw [coe_J3, Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.transpose_apply]

@[expose] noncomputable def gam' (F : Type) [Field F] : MulAut SL(3, F) :=
  MulAut.conj (J3 F) * gam F

theorem coe_gam' (y : SL(3, F)) : ((gam' F y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    (J3 F : Matrix (Fin 3) (Fin 3) F) *
      ((y⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose *
        (((J3 F)⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem gam'_sq_blockSL :
    gam' F * gam' F = MulAut.conj (blockSL F 3 2 0 (by omega) (-1)) := by
  have key : ∀ (b : MulAut SL(3, F)) (m : SL(3, F)),
      b * MulAut.conj m = MulAut.conj (b m) * b := by
    intro b m
    ext x
    simp [MulAut.conj_apply]
  have h1 : gam F * gam F = 1 := by
    refine MulEquiv.ext fun x => ?_
    exact gam_gam x
  calc gam' F * gam' F = MulAut.conj (J3 F) * (gam F * MulAut.conj (J3 F)) * gam F := by
        simp [gam', mul_assoc]
    _ = MulAut.conj (J3 F) * (MulAut.conj (gam F (J3 F)) * gam F) * gam F := by
        rw [key]
    _ = MulAut.conj (J3 F) * MulAut.conj (J3 F) * (gam F * gam F) := by
        rw [gam_J3]; simp [mul_assoc]
    _ = MulAut.conj (blockSL F 3 2 0 (by omega) (-1)) := by
        rw [h1, mul_one, ← map_mul, J3_mul_J3]

theorem gam'_blockSL (A : SL(2, F)) :
    gam' F (blockSL F 3 2 0 (by omega) A) = blockSL F 3 2 0 (by omega) A := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  apply Subtype.ext
  show (J3 F).1 * (adjugate (blockSL F 3 2 0 (by omega) A).1)ᵀ * adjugate (J3 F).1 =
    (blockSL F 3 2 0 (by omega) A).1
  rw [coe_J3, coe_blockSL_three_zero]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.transpose_apply, -Matrix.cons_mul, -Matrix.vecMul_cons, -Matrix.cons_vecMul]
  linear_combination hdet

abbrev rootSL2₃ (F : Type) [Field F] : Subgroup SL(3, F) :=
  rootSL2 F (n := 3) (by norm_num)

noncomputable abbrev rootInv₃ (F : Type) [Field F] : SL(3, F) :=
  rootInv F (n := 3) (by norm_num)

theorem gam'_sq : gam' F * gam' F = MulAut.conj (rootInv₃ F) := gam'_sq_blockSL

theorem gam'_apply_of_mem_rootSL2 {r : SL(3, F)} (hr : r ∈ rootSL2₃ F) : gam' F r = r := by
  obtain ⟨A, rfl⟩ := hr
  exact gam'_blockSL A

theorem rootInv₃_mul_self : rootInv₃ F * rootInv₃ F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem rootInv₃_ne_one (h2 : (2 : F) ≠ 0) : rootInv₃ F ≠ 1 := by
  intro h
  have h1 := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp only [coe_rootInv_three, Matrix.SpecialLinearGroup.coe_one] at h1
  have h3 : (-1 : F) = 1 := by simpa using h1
  apply h2
  linear_combination -h3

theorem rootInv₃_mem : rootInv₃ F ∈ rootSL2₃ F := rootInv_mem_rootSL2 _

theorem mem_centralizer_rootSL2₃ {g : SL(3, F)} (hg : ∀ r ∈ rootSL2₃ F, g * r = r * g) :
    g ∈ Subgroup.centralizer (rootSL2₃ F : Set SL(3, F)) :=
  Subgroup.mem_centralizer_iff.mpr fun r hr => (hg r hr).symm

theorem gam'_eq_inv_of_isBlockScalar {y : SL(3, F)}
    (hy : IsBlockScalar ((y⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) : gam' F y = y⁻¹ := by
  apply Subtype.ext
  have hJ : IsBlockDiag ((J3 F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [coe_J3]
    simp [IsBlockDiag]
  rw [coe_gam', transpose_eq_of_isBlockScalar hy, commute_of_isBlockDiag hJ hy, Matrix.mul_assoc,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_one]

theorem gam'_eq_inv_of_commutes {g : SL(3, F)} (hg : ∀ r ∈ rootSL2₃ F, g * r = r * g) :
    gam' F g = g⁻¹ :=
  gam'_eq_inv_of_isBlockScalar (isBlockScalar_of_mem_centralizer
    (Subgroup.inv_mem _ (mem_centralizer_rootSL2₃ hg)))

theorem isBlockScalar_sq_eq_one {M : Matrix (Fin 3) (Fin 3) F} (hM : IsBlockScalar M)
    (hdet : M.det = 1) (hsq : M * M = 1) :
    M = 1 ∨ M = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  obtain ⟨h01, h02, h10, h12, h20, h21, h00⟩ := hM
  have e00 := congrFun (congrFun hsq 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h20, mul_zero, add_zero,
    Matrix.one_apply_eq] at e00
  rw [Matrix.det_fin_three] at hdet
  simp only [h01, h02, h10, h12, h20, h21, mul_zero, zero_mul, sub_zero, add_zero] at hdet
  have he : M 2 2 = 1 := by
    rw [← h00] at hdet
    linear_combination hdet - M 2 2 * e00
  rcases mul_self_eq_one_iff.mp e00 with ha | ha
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, ha, ← h00, he]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, ha, ← h00, he]

theorem eq_one_or_rootInv_of_commutes {g : SL(3, F)} (hg : ∀ r ∈ rootSL2₃ F, g * r = r * g)
    (hg2 : g * g = 1) : g = 1 ∨ g = rootInv₃ F := by
  have hbs := isBlockScalar_of_mem_centralizer (mem_centralizer_rootSL2₃ hg)
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
  have hsq : (g : Matrix (Fin 3) (Fin 3) F) * g = 1 := by
    have := congrArg (fun z : SL(3, F) => (z : Matrix (Fin 3) (Fin 3) F)) hg2
    simpa using this
  rcases isBlockScalar_sq_eq_one hbs hdet hsq with h | h
  · left
    exact Subtype.ext (by simpa using h)
  · right
    exact Subtype.ext (by rw [coe_rootInv_three]; exact h)

theorem center_sl3_eq_bot [Finite F] (hF : Nat.card F = 3) : Subgroup.center SL(3, F) = ⊥ := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have hrr : r ^ 3 = r := by simpa [hF'] using FiniteField.pow_card r
  have hr1 : r = 1 := by rw [← hrr]; exact hr3
  subst hr1
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by rw [← hrz]; simp)

end CFSG.ClassicalInvolution.Q3.Q3PP
