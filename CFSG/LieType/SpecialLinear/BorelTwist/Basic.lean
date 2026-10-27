module

public import CFSG.LieType.SpecialLinear.CurtisDatum
public import CFSG.LieType.SpecialLinear.Block222.Borel.Graph

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

variable {n : ℕ} {F : Type} [Field F]

theorem revGL_mul_mul (X : Matrix (Fin n) (Fin n) F) :
    LinearFlag.permMatrix n F Fin.revPerm * X * LinearFlag.permMatrix n F Fin.revPerm =
      X.submatrix Fin.rev Fin.rev := by
  rw [LinearFlag.permMatrix_eq, Equiv.Perm.inv_def, Fin.revPerm_symm, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  congr 1

theorem revGL_conj_single (i j : Fin n) (c : F) :
    LinearFlag.permMatrix n F Fin.revPerm * Matrix.single i j c *
        LinearFlag.permMatrix n F Fin.revPerm =
      Matrix.single (Fin.rev i) (Fin.rev j) c := by
  rw [revGL_mul_mul]
  change (Matrix.single i j c).submatrix Fin.revPerm Fin.revPerm =
    Matrix.single (Fin.rev i) (Fin.rev j) c
  rw [Matrix.submatrix_single_equiv]
  rfl

theorem borelGraph_transvection {i j : Fin n} (hij : i ≠ j) (c : F) :
    borelGraph n F (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (fun h => hij (Fin.rev_injective h).symm) (-c) := by
  apply Subtype.ext
  rw [coe_borelGraph, revGL_inv F n, coe_revGL, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, permMatrix_rev_mul_self F n,
    revGL_conj_single]
  rw [SpecialLinearGroup.transvection_coe]

section RankOne

variable (m : ℕ) (F : Type) [Field F]

theorem hdiag_inv (s : Fin m) (u : Fˣ) :
    (hdiag m F s u)⁻¹ = hdiag m F s u⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← hdiag_mul, mul_inv_cancel, hdiag_one]

theorem hdiag_matrix (s : Fin m) (u : Fˣ) :
    ((hdiag m F s u : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.diagonal (fun i => if i = s.castSucc then (u : F)
        else if i = s.succ then ((u⁻¹ : Fˣ) : F) else 1) := by
  rw [hdiag, SpecialLinearGroup.diag2nUnit_coe]

theorem revGL_conj_diagonal (d : Fin n → F) :
    LinearFlag.permMatrix n F Fin.revPerm * Matrix.diagonal d *
        LinearFlag.permMatrix n F Fin.revPerm =
      Matrix.diagonal (fun i => d (Fin.rev i)) := by
  rw [revGL_mul_mul, Matrix.submatrix_diagonal _ Fin.rev Fin.rev_injective]
  rfl

theorem castSucc_rev (s : Fin m) :
    (Fin.rev s).castSucc = Fin.rev (Fin.succ s) := by
  ext
  simp [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
  try omega

theorem succ_rev (s : Fin m) :
    (Fin.rev s).succ = Fin.rev (Fin.castSucc s) := by
  ext
  simp [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
  try omega

theorem borelGraph_hdiag (s : Fin m) (u : Fˣ) :
    borelGraph (m + 1) F (hdiag m F s u) = hdiag m F (Fin.rev s) u := by
  apply Subtype.ext
  rw [coe_borelGraph, revGL_inv F (m + 1), coe_revGL, hdiag_inv, hdiag_matrix,
    Matrix.diagonal_transpose,
    revGL_conj_diagonal, hdiag_matrix]
  congr 1
  funext i
  simp only [Fin.rev_eq_iff, castSucc_rev, succ_rev, inv_inv]
  by_cases h1 : i = s.rev.castSucc
  · simp [h1, ← castSucc_rev, ← succ_rev, Fin.castSucc_lt_succ.ne]
  · by_cases h2 : i = s.rev.succ
    · simp [h2, ← castSucc_rev, ← succ_rev, (Fin.castSucc_lt_succ (i := s.rev)).ne.symm]
    · simp [h1, h2, ← castSucc_rev, ← succ_rev]

end RankOne

section Weyl

variable (m : ℕ) (F : Type) [Field F]

open CFSG.LieType.Universal.SpecialLinear

theorem coe_weylRep' (s : Fin m) :
    ((weylRep m F s : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      weylMatrix s.castSucc s.succ :=
  coe_transvection_mul_transvection_mul_transvection (Fin.castSucc_lt_succ.ne)

theorem weylSign_eq_one [CharP F 2] (a s : Fin (m + 1)) :
    weylSign (R := F) a s = 1 := by
  have h : weylSign (R := F) a s ^ 2 = 1 := by
    rw [pow_two]
    exact weylSign_mul_self a s
  rcases (sq_eq_one_iff.mp h) with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

theorem weylMatrix_eq_permMatrix [CharP F 2] (a b : Fin (m + 1)) :
    weylMatrix (R := F) a b = LinearFlag.permMatrix (m + 1) F (Equiv.swap a b) := by
  ext r s
  rw [weylMatrix, signedPerm_apply, LinearFlag.permMatrix_apply, weylSign_eq_one]

theorem transpose_permMatrix_swap (a b : Fin (m + 1)) :
    (LinearFlag.permMatrix (m + 1) F (Equiv.swap a b))ᵀ =
      LinearFlag.permMatrix (m + 1) F (Equiv.swap a b) := by
  ext i j
  simp only [Matrix.transpose_apply, LinearFlag.permMatrix_apply]
  have hiff : i = (Equiv.swap a b) j ↔ j = (Equiv.swap a b) i := by
    rw [eq_comm, Equiv.swap_apply_eq_iff]
  by_cases h : i = (Equiv.swap a b) j
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem permMatrix_submatrix_rev (σ : Equiv.Perm (Fin (m + 1))) :
    (LinearFlag.permMatrix (m + 1) F σ).submatrix Fin.rev Fin.rev =
      LinearFlag.permMatrix (m + 1) F (Fin.revPerm * σ * Fin.revPerm) := by
  ext x y
  simp only [Matrix.submatrix_apply, LinearFlag.permMatrix_apply, Equiv.Perm.mul_apply,
    Fin.revPerm_apply, Fin.rev_eq_iff]

theorem weylRep_mul_self_charTwo [CharP F 2] (s : Fin m) :
    weylRep m F s * weylRep m F s = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_weylRep',
    weylMatrix_mul_self (a := s.castSucc) (b := s.succ) Fin.castSucc_lt_succ.ne]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, CharTwo.neg_eq]

theorem weylRep_inv_charTwo [CharP F 2] (s : Fin m) :
    (weylRep m F s)⁻¹ = weylRep m F s :=
  inv_eq_of_mul_eq_one_right (weylRep_mul_self_charTwo m F s)

theorem swap_mul_perm_mul_inv {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (a b : α) :
    σ * Equiv.swap a b * σ⁻¹ = Equiv.swap (σ a) (σ b) := by
  ext i
  by_cases h1 : i = σ a
  · subst h1
    simp
  · by_cases h2 : i = σ b
    · subst h2
      simp
    · have h1' : σ.symm i ≠ a := fun h => h1 (by rw [← h, σ.apply_symm_apply])
      have h2' : σ.symm i ≠ b := fun h => h2 (by rw [← h, σ.apply_symm_apply])
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, h2, h1', h2']
      exact h1

theorem revPerm_swap_conj (a b : Fin (m + 1)) :
    Fin.revPerm * Equiv.swap a b * Fin.revPerm =
      Equiv.swap (Fin.rev a) (Fin.rev b) := by
  have h := swap_mul_perm_mul_inv (σ := (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) a b
  have hinv : (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹ = Fin.revPerm := Fin.revPerm_symm
  rw [hinv] at h
  simpa [Fin.revPerm_apply] using h

theorem borelGraph_weylRep [CharP F 2] (s : Fin m) :
    borelGraph (m + 1) F (weylRep m F s) = weylRep m F (Fin.rev s) := by
  apply Subtype.ext
  rw [coe_borelGraph, revGL_inv F (m + 1), coe_revGL, weylRep_inv_charTwo, coe_weylRep',
    weylMatrix_eq_permMatrix,
    transpose_permMatrix_swap, revGL_mul_mul, permMatrix_submatrix_rev, revPerm_swap_conj,
    coe_weylRep', weylMatrix_eq_permMatrix]
  congr 1
  rw [castSucc_rev, succ_rev, Equiv.swap_comm]

end Weyl

theorem borelGraph_eq_slConjugation_mul_slGraph :
    borelGraph n F =
      CatalogueBHigherLinearAction.slConjugation n F (revGL n F) *
        CatalogueBGraphForm.slGraphAut n F := by
  have hf : CatalogueBHigherLinearField.slFieldAut (Fin n) F (RingEquiv.refl F) = 1 := by
    rw [show (RingEquiv.refl F) = 1 from rfl, map_one]
  simp only [borelGraph, CFSG.QuasithinUnique.K1.stdAut, hf, mul_one, pow_one]

theorem glFieldEquiv_revGL (σ : F ≃+* F) :
    CatalogueBHigherLinearField.glFieldEquiv (Fin n) σ (revGL n F) = revGL n F := by
  apply Units.ext
  ext i j
  rw [CatalogueBHigherLinearField.glFieldEquiv_entry, coe_revGL, LinearFlag.permMatrix_apply]
  by_cases h : i = Fin.revPerm j <;> simp [h]

theorem slFieldAut_mul_slConjugation_revGL (σ : F ≃+* F) :
    CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
        CatalogueBHigherLinearAction.slConjugation n F (revGL n F) =
      CatalogueBHigherLinearAction.slConjugation n F (revGL n F) *
        CatalogueBHigherLinearField.slFieldAut (Fin n) F σ := by
  have h := LinearFlag.slField_mul_slConjugation_mul_inv (n := n) (K := F) σ (revGL n F)
  rw [glFieldEquiv_revGL] at h
  calc CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
        CatalogueBHigherLinearAction.slConjugation n F (revGL n F)
      = (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
          CatalogueBHigherLinearAction.slConjugation n F (revGL n F) *
          (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ)⁻¹) *
          CatalogueBHigherLinearField.slFieldAut (Fin n) F σ := by group
    _ = CatalogueBHigherLinearAction.slConjugation n F (revGL n F) *
          CatalogueBHigherLinearField.slFieldAut (Fin n) F σ := by rw [h]

theorem stdAut_one_eq_borelStd (A : GL (Fin n) F) (σ : F ≃+* F) :
    CFSG.QuasithinUnique.K1.stdAut A σ 1 =
      borelStd n F (A * (revGL n F)⁻¹) σ 1 := by
  have hFP := slFieldAut_mul_slConjugation_revGL (n := n) (F := F) σ
  have hstd : CFSG.QuasithinUnique.K1.stdAut A σ 1 =
      CatalogueBHigherLinearAction.slConjugation n F A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
        CatalogueBGraphForm.slGraphAut n F := by
    rw [CFSG.QuasithinUnique.K1.stdAut]
    simp
  have hborel : borelStd n F (A * (revGL n F)⁻¹) σ 1 =
      (CatalogueBHigherLinearAction.slConjugation n F (A * (revGL n F)⁻¹) *
        CatalogueBHigherLinearField.slFieldAut (Fin n) F σ) *
        (CatalogueBHigherLinearAction.slConjugation n F (revGL n F) *
          CatalogueBGraphForm.slGraphAut n F) := by
    rw [borelStd, borelGraph_eq_slConjugation_mul_slGraph]
    simp [CFSG.QuasithinUnique.K1.stdAut]
  rw [hstd, hborel]
  symm
  calc
    (CatalogueBHigherLinearAction.slConjugation n F (A * (revGL n F)⁻¹) *
        CatalogueBHigherLinearField.slFieldAut (Fin n) F σ) *
        (CatalogueBHigherLinearAction.slConjugation n F (revGL n F) *
          CatalogueBGraphForm.slGraphAut n F)
      = CatalogueBHigherLinearAction.slConjugation n F (A * (revGL n F)⁻¹) *
          (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
            CatalogueBHigherLinearAction.slConjugation n F (revGL n F)) *
          CatalogueBGraphForm.slGraphAut n F := by group
    _ = CatalogueBHigherLinearAction.slConjugation n F (A * (revGL n F)⁻¹) *
          (CatalogueBHigherLinearAction.slConjugation n F (revGL n F) *
            CatalogueBHigherLinearField.slFieldAut (Fin n) F σ) *
          CatalogueBGraphForm.slGraphAut n F := by rw [hFP]
    _ = (CatalogueBHigherLinearAction.slConjugation n F (A * (revGL n F)⁻¹) *
          CatalogueBHigherLinearAction.slConjugation n F (revGL n F)) *
          CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
          CatalogueBGraphForm.slGraphAut n F := by group
    _ = CatalogueBHigherLinearAction.slConjugation n F A *
          CatalogueBHigherLinearField.slFieldAut (Fin n) F σ *
          CatalogueBGraphForm.slGraphAut n F := by
        rw [← map_mul]
        rw [show A * (revGL n F)⁻¹ * revGL n F = A by group]

section Borel

variable (m : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2]

theorem borelGraph_mem_U {g : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : g ∈ (curtisDatum m F 2).U) :
    borelGraph (m + 1) F g ∈ (curtisDatum m F 2).U := by
  have hginv : g⁻¹ ∈ (curtisDatum m F 2).U := inv_mem hg
  rw [mem_curtisDatum_U_iff] at hg ⊢
  have hg' := (mem_curtisDatum_U_iff (m := m) (F := F) (p := 2)).mp hginv
  refine ⟨?_, ?_⟩
  · intro i
    rw [coe_borelGraph, revGL_inv F (m + 1), coe_revGL, revGL_mul_mul, Matrix.submatrix_apply,
      Matrix.transpose_apply]
    exact hg'.1 (Fin.rev i)
  · intro i j hji
    rw [coe_borelGraph, revGL_inv F (m + 1), coe_revGL, revGL_mul_mul, Matrix.submatrix_apply,
      Matrix.transpose_apply]
    exact hg'.2 (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.mpr hji)

theorem borelGraph_mem_H {g : SpecialLinearGroup (Fin (m + 1)) F}
    (hg : g ∈ (curtisDatum m F 2).H) :
    borelGraph (m + 1) F g ∈ (curtisDatum m F 2).H := by
  have hginv : g⁻¹ ∈ (curtisDatum m F 2).H := inv_mem hg
  rw [mem_curtisDatum_H_iff] at hg ⊢
  have hg' := (mem_curtisDatum_H_iff (m := m) (F := F) (p := 2)).mp hginv
  intro i j hij
  rw [coe_borelGraph, revGL_inv F (m + 1), coe_revGL, revGL_mul_mul, Matrix.submatrix_apply,
    Matrix.transpose_apply]
  exact hg' (Fin.rev j) (Fin.rev i) (fun h => hij (Fin.rev_injective h).symm)

end Borel

end CFSG.LieType.SpecialLinear
