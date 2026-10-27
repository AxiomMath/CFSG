module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialitySpin
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightAutTori

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.Universal.Spin
open CFSG.LieType.RootSystem (roots)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap (plusSwapDerived plusSwapMatrix
  plusSwapPerm plusSwapDerived_val plusSwapMatrix_inv coe_plusSwapMatrix)
open CFSG.ComponentClassification.UnbalancedCatalog (symmetryGL symmetryAut symmetryIsometry
  symmetryGL_mul_self)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

section Equiv

variable {F : Type} [Field F] [CharP F 2]

theorem spinMatrix_quadPlus_four_injective : Function.Injective (spinMatrix (quadPlus 4 F)) :=
  (MonoidHom.ker_eq_bot_iff _).1 (ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero)

variable (F) in
@[expose] noncomputable def spin8OmegaEquiv :
    spinGroup (quadPlus 4 F) ≃* StatedOmega (StatedQuadPlus 4 F) :=
  (MonoidHom.ofInjective spinMatrix_quadPlus_four_injective).trans
    (MulEquiv.subgroupCongr (range_spinMatrix_quadPlus d4_three_le))

theorem coe_spin8OmegaEquiv (g : spinGroup (quadPlus 4 F)) :
    ((spin8OmegaEquiv F g : StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F) =
      spinMatrix (quadPlus 4 F) g := rfl

variable (F) in
@[expose] noncomputable def spin8Equiv :
    spinGroup (quadPlus 4 F) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F) :=
  (spin8OmegaEquiv F).trans (statedOmegaPlusEquiv F 4 (by norm_num))

theorem spin8Equiv_apply (g : spinGroup (quadPlus 4 F)) :
    spin8Equiv F g = statedOmegaPlusEquiv F 4 (by norm_num) (spin8OmegaEquiv F g) := rfl

end Equiv

section RootMat

variable {F : Type} [Field F]

variable (F) in
@[expose] def spin8RootMat (i j : Fin 4) (s t : Bool) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F :=
  Matrix.single (SpinPlus.plusIdx i s) (SpinPlus.plusIdx j (!t)) 1 +
    Matrix.single (SpinPlus.plusIdx j t) (SpinPlus.plusIdx i (!s)) 1

variable [CharP F 2]

theorem coe_spinMatrix_spin8X {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (hγ : toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : F) :
    (spinMatrix (quadPlus 4 F) (SpinPlus.x 4 F d4_three_le γ c) : Matrix _ _ F) =
      1 + c • spin8RootMat F i j s t := by
  rw [SpinPlus.x, coe_spinMatrix_rootElt (SpinPlus.isCoordFrame_plusFrame d4_three_le),
    rootMat_eq (SpinPlus.isCoordFrame_plusFrame d4_three_le) hij hγ]
  have hr : (repSign i j s t : F) = 1 := by
    rcases repSign_eq_one_or_eq_neg_one i j s t with h | h <;> rw [h]
    · simp
    · simp [CharTwo.neg_eq]
  rw [hr, one_smul]
  congr 2
  ext a b
  simp only [longMat, spin8RootMat, Matrix.sub_apply, Matrix.add_apply]
  exact CharTwo.sub_eq_add _ _

theorem spinMatrix_x_mulVec {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (hγ : toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : F)
    (v : Fin 4 ⊕ Fin 4 → F) :
    (spinMatrix (quadPlus 4 F) (SpinPlus.x 4 F d4_three_le γ c) : Matrix _ _ F) *ᵥ v =
      v + c • (Pi.single (SpinPlus.plusIdx i s) (v (SpinPlus.plusIdx j (!t))) +
        Pi.single (SpinPlus.plusIdx j t) (v (SpinPlus.plusIdx i (!s)))) := by
  rw [coe_spinMatrix_spin8X hij hγ, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    spin8RootMat, Matrix.add_mulVec, Matrix.single_mulVec, Matrix.single_mulVec, one_mul, one_mul]
  rfl

theorem exists_toStdD_eq_of_mem_roots {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) :
    ∃ (i j : Fin 4) (_ : i ≠ j) (s t : Bool),
      toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) :=
  (SpinPlus.isLong_toStdD_iff (by norm_num)).2 hγ

end RootMat

section Field

variable {F : Type} [Field F] [CharP F 2]

theorem statedFieldConj_spin8OmegaEquiv_x (σ : F ≃+* F) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) (c : F) :
    statedFieldConj σ (spin8OmegaEquiv F (SpinPlus.x 4 F d4_three_le γ c)) =
      spin8OmegaEquiv F (SpinPlus.x 4 F d4_three_le γ (σ c)) := by
  obtain ⟨i, j, hij, s, t, he⟩ := exists_toStdD_eq_of_mem_roots hγ
  apply Subtype.ext
  apply Units.ext
  ext a b
  rw [statedFieldConj_entry]
  change σ ((spinMatrix (quadPlus 4 F) (SpinPlus.x 4 F d4_three_le γ c) : Matrix _ _ F) a b) =
    (spinMatrix (quadPlus 4 F) (SpinPlus.x 4 F d4_three_le γ (σ c)) : Matrix _ _ F) a b
  rw [coe_spinMatrix_spin8X hij he, coe_spinMatrix_spin8X hij he]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, spin8RootMat,
    Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem fieldAutHom_spin8Equiv_x (σ : F ≃+* F) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) (c : F) :
    fieldAutHom F 4 σ (spin8Equiv F (SpinPlus.x 4 F d4_three_le γ c)) =
      spin8Equiv F (SpinPlus.x 4 F d4_three_le γ (σ c)) := by
  rw [spin8Equiv_apply, fieldAutHom_statedOmegaPlusEquiv, statedFieldConj_spin8OmegaEquiv_x σ hγ]
  rfl

end Field

section Fork

@[expose] def forkFlip (m : Fin 4) (r : Bool) : Bool := if m = 3 then !r else r

theorem forkFlip_not (m : Fin 4) (r : Bool) : forkFlip m (!r) = !forkFlip m r := by
  unfold forkFlip
  split_ifs <;> rfl

theorem boolSign_forkFlip (m : Fin 4) (r : Bool) :
    boolSign (forkFlip m r) = if m = 3 then -boolSign r else boolSign r := by
  unfold forkFlip
  split_ifs <;> simp

theorem toStdD_fundPerm_d4ForkPerm (v : Fin 4 → ℤ) :
    toStdD 4 (fundPerm d4ForkPerm v) = fun a => if a = 3 then -toStdD 4 v a else toStdD 4 v a := by
  funext a
  fin_cases a
  all_goals simp [toStdD, fundPerm_apply, d4ForkPerm, Equiv.swap_apply_def]
  all_goals ring

theorem toStdD_fundPerm_d4ForkPerm_eq {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (hγ : toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    toStdD 4 (fundPerm d4ForkPerm γ) =
      Pi.single i (boolSign (forkFlip i s)) + Pi.single j (boolSign (forkFlip j t)) := by
  rw [toStdD_fundPerm_d4ForkPerm, hγ]
  funext a
  simp only [Pi.add_apply, Pi.single_apply, boolSign_forkFlip]
  by_cases hai : a = i
  · subst hai
    simp only [ite_true, hij, ite_false, add_zero]
  · by_cases haj : a = j
    · subst haj
      simp only [ite_true, hai, ite_false, zero_add]
    · simp [hai, haj]

theorem plusSwapPerm_four_plusIdx (m : Fin 4) (r : Bool) :
    plusSwapPerm 4 (by norm_num) (SpinPlus.plusIdx m r) = SpinPlus.plusIdx m (forkFlip m r) := by
  revert m r
  decide

variable {F : Type} [Field F]

theorem swap_permMatrix_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι)
    (M : Matrix ι ι F) :
    (Equiv.swap a b).permMatrix F * M * (Equiv.swap a b).permMatrix F =
      M.submatrix (Equiv.swap a b) (Equiv.swap a b) := by
  simp only [Equiv.Perm.permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix,
    Equiv.symm_swap]
  rfl

theorem submatrix_one_add_smul_single_add_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (c : F) (x y z w : ι) :
    (1 + c • (Matrix.single x y (1 : F) + Matrix.single z w 1)).submatrix σ σ =
      1 + c • (Matrix.single (σ.symm x) (σ.symm y) 1 + Matrix.single (σ.symm z) (σ.symm w) 1) := by
  have h1 := Matrix.submatrix_single_equiv σ σ x y (1 : F)
  have h2 := Matrix.submatrix_single_equiv σ σ z w (1 : F)
  have h3 := Matrix.submatrix_one_equiv (α := F) σ
  ext a b
  have e1 := congrFun (congrFun h1 a) b
  have e2 := congrFun (congrFun h2 a) b
  have e3 := congrFun (congrFun h3 a) b
  simp only [Matrix.submatrix_apply] at e1 e2 e3 ⊢
  simp only [Matrix.add_apply, Matrix.smul_apply, e1, e2, e3]

variable [CharP F 2]

theorem plusSwapDerived_spin8OmegaEquiv_x {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) (c : F) :
    plusSwapDerived 4 F (by norm_num) (spin8OmegaEquiv F (SpinPlus.x 4 F d4_three_le γ c)) =
      spin8OmegaEquiv F (SpinPlus.x 4 F d4_three_le (fundPerm d4ForkPerm γ) c) := by
  obtain ⟨i, j, hij, s, t, he⟩ := exists_toStdD_eq_of_mem_roots hγ
  have he' := toStdD_fundPerm_d4ForkPerm_eq hij he
  apply Subtype.ext
  apply Units.ext
  rw [plusSwapDerived_val, Units.val_mul, Units.val_mul, plusSwapMatrix_inv, coe_plusSwapMatrix,
    coe_spin8OmegaEquiv, coe_spin8OmegaEquiv, coe_spinMatrix_spin8X hij he,
    coe_spinMatrix_spin8X hij he']
  rw [plusSwapPerm, swap_permMatrix_mul_mul, spin8RootMat, spin8RootMat,
    submatrix_one_add_smul_single_add_single, Equiv.symm_swap]
  have h1 : ∀ m r, Equiv.swap (Sum.inl (⟨4 - 1, by norm_num⟩ : Fin 4))
      (Sum.inr (⟨4 - 1, by norm_num⟩ : Fin 4)) (SpinPlus.plusIdx m r) =
        SpinPlus.plusIdx m (forkFlip m r) := plusSwapPerm_four_plusIdx
  rw [h1, h1, h1, h1, forkFlip_not, forkFlip_not]

end Fork

section Kappa

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem statedDerivedPlusEquiv_entry_plusIndex {m : ℕ} (A : StatedOmega (StatedQuadPlus m F))
    (i j : Fin m ⊕ Fin m) :
    ((statedDerivedPlusEquiv F m A : matrixDerived (coordinateQuadPlus m F)) :
        GL (Fin (2 * m)) F).val (plusIndexEquiv m i) (plusIndexEquiv m j) =
      (A : GL (Fin m ⊕ Fin m) F).val i j := by
  have h := statedDerivedPlusEquiv_symm_entry F m (statedDerivedPlusEquiv F m A) i j
  rw [MulEquiv.symm_apply_apply] at h
  exact h.symm

theorem coe_symmetryGL_lastPlaneVec :
    ((symmetryGL (coordinateQuadPlus (3 + 1) F) (lastPlaneVec 3) : GL (Fin (2 * (3 + 1))) F) :
        Matrix _ _ F) =
      (Equiv.swap (plusIndexEquiv (3 + 1) (.inl (Fin.last 3)))
        (plusIndexEquiv (3 + 1) (.inr (Fin.last 3)))).permMatrix F := by
  have h := symmetryGL_lastPlaneVec_eq_swapLin (F := F) (r := 3)
  have key : ∀ w : Fin (2 * (3 + 1)) → F,
      ((symmetryGL (coordinateQuadPlus (3 + 1) F) (lastPlaneVec 3) : GL (Fin (2 * (3 + 1))) F) :
          Matrix _ _ F) *ᵥ w =
        (Equiv.swap (plusIndexEquiv (3 + 1) (.inl (Fin.last 3)))
          (plusIndexEquiv (3 + 1) (.inr (Fin.last 3)))).permMatrix F *ᵥ w := by
    intro w
    have h1 := LinearEquiv.congr_fun h w
    rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.matrixLinearIso_apply_eq,
      matrixLinearEquiv_apply] at h1
    rw [h1, Matrix.permMatrix_mulVec]
    funext a
    rw [swapLin_apply]
    rfl
  refine Matrix.ext fun a b => ?_
  have h2 := congrFun (key (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using h2

theorem symmetryAut_statedOmegaPlusEquiv (A : StatedOmega (StatedQuadPlus 4 F)) :
    symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3)
        (statedOmegaPlusEquiv F 4 (by norm_num) A) =
      statedOmegaPlusEquiv F 4 (by norm_num) (plusSwapDerived 4 F (by norm_num) A) := by
  have hSS : (symmetryGL (coordinateQuadPlus (3 + 1) F) (lastPlaneVec 3))⁻¹ =
      symmetryGL (coordinateQuadPlus (3 + 1) F) (lastPlaneVec 3) :=
    inv_eq_of_mul_eq_one_right (symmetryGL_mul_self _ _)
  change matrixProjectiveConjugation _
      (matrixIsometryInclusion _ (symmetryIsometry _ (lastPlaneVec 3)))
      (matrixProjectiveProjection _ (statedDerivedPlusEquiv F 4 A)) =
    matrixProjectiveProjection _ (statedDerivedPlusEquiv F 4 (plusSwapDerived 4 F (by norm_num) A))
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply Subtype.ext
  rw [matrixDerivedConjugation_val]
  change symmetryGL (coordinateQuadPlus (3 + 1) F) (lastPlaneVec 3) *
      glFieldAut (Fin (2 * (3 + 1))) F 1 (statedDerivedPlusEquiv F 4 A).val *
      (symmetryGL (coordinateQuadPlus (3 + 1) F) (lastPlaneVec 3))⁻¹ = _
  rw [map_one, MulAut.one_apply, hSS]
  apply Units.ext
  ext a b
  obtain ⟨i, rfl⟩ := (plusIndexEquiv (3 + 1)).surjective a
  obtain ⟨j, rfl⟩ := (plusIndexEquiv (3 + 1)).surjective b
  rw [Units.val_mul, Units.val_mul, coe_symmetryGL_lastPlaneVec, swap_permMatrix_mul_mul,
    Matrix.submatrix_apply, (plusIndexEquiv (3 + 1)).injective.swap_apply,
    (plusIndexEquiv (3 + 1)).injective.swap_apply]
  rw [statedDerivedPlusEquiv_entry_plusIndex, statedDerivedPlusEquiv_entry_plusIndex,
    plusSwapDerived_val,
    Units.val_mul, Units.val_mul, plusSwapMatrix_inv, coe_plusSwapMatrix, plusSwapPerm,
    swap_permMatrix_mul_mul, Matrix.submatrix_apply]
  rfl

theorem symmetryAut_spin8Equiv_x {γ : Fin 4 → ℤ} (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots)
    (c : F) :
    symmetryAut (coordinateQuadPlus 4 F) (lastPlaneVec 3)
        (spin8Equiv F (SpinPlus.x 4 F d4_three_le γ c)) =
      spin8Equiv F (SpinPlus.x 4 F d4_three_le (fundPerm d4ForkPerm γ) c) := by
  rw [spin8Equiv_apply, symmetryAut_statedOmegaPlusEquiv, plusSwapDerived_spin8OmegaEquiv_x hγ]
  rfl

end Kappa

end CFSG.SeitzReduction.OmegaPilot
