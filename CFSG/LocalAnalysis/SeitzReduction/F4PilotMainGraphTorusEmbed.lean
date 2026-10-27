module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusGram
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLinear
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective mat_equiv_diagonal)

section SL6

variable {F : Type} [Field F]

@[expose] def sp6ToSLIdx : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

theorem sp6ToSLIdx_inl (i : Fin 3) : sp6ToSLIdx (.inl i) = Fin.castAdd 3 i :=
  finSumFinEquiv_apply_left i

theorem sp6ToSLIdx_inr (i : Fin 3) : sp6ToSLIdx (.inr i) = Fin.natAdd 3 i :=
  finSumFinEquiv_apply_right i

theorem sp6ToSL_det_mat {n : ℕ} (A : StatedSp n F) : (mat n F A).det = 1 := by
  have hsp := TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.1
    ((Subgroup.ext_iff.1 CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic _).1 A.2)
  exact SymplecticGroup.det_eq_one hsp

theorem sp6ToSL_mat_symplectic {n : ℕ} (A : StatedSp n F) :
    (mat n F A)ᵀ * fromBlocks 0 1 (-1) 0 * mat n F A = fromBlocks 0 1 (-1) 0 :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 A.2

@[expose] noncomputable def sp6ToSL6 : StatedSp 3 F →* SpecialLinearGroup (Fin 6) F where
  toFun A := ⟨Matrix.reindexAlgEquiv F F sp6ToSLIdx (mat 3 F A), by
    rw [Matrix.det_reindexAlgEquiv, sp6ToSL_det_mat]⟩
  map_one' := Subtype.ext (by
    change Matrix.reindexAlgEquiv F F sp6ToSLIdx (mat 3 F 1) = 1
    rw [map_one, map_one])
  map_mul' A B := Subtype.ext (by
    change Matrix.reindexAlgEquiv F F sp6ToSLIdx (mat 3 F (A * B)) =
      Matrix.reindexAlgEquiv F F sp6ToSLIdx (mat 3 F A) *
        Matrix.reindexAlgEquiv F F sp6ToSLIdx (mat 3 F B)
    rw [map_mul, map_mul])

theorem coe_sp6ToSL6 (A : StatedSp 3 F) :
    (sp6ToSL6 A : Matrix (Fin 6) (Fin 6) F) = Matrix.reindexAlgEquiv F F sp6ToSLIdx (mat 3 F A) :=
  rfl

theorem sp6ToSL6_injective : Function.Injective (sp6ToSL6 (F := F)) := by
  intro A B h
  apply mat_injective
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 6) F => (g : Matrix (Fin 6) (Fin 6) F)) h
  simp only [coe_sp6ToSL6] at h'
  exact (Matrix.reindexAlgEquiv F F sp6ToSLIdx).injective h'

theorem sp6ToSL_mat_sp6Diag (t : Fin 3 → Fˣ) :
    mat 3 F (sp6Diag F t) =
      Matrix.diagonal (Sum.elim (fun i => (t i : F)) (fun i => (((t i)⁻¹ : Fˣ) : F))) :=
  mat_equiv_diagonal t

theorem sp6ToSL6_sp6Diag (t : Fin 3 → Fˣ) : sp6ToSL6 (sp6Diag F t) = lin6Torus F t := by
  apply Subtype.ext
  rw [coe_sp6ToSL6, sp6ToSL_mat_sp6Diag, lin6Torus, coe_diagTorusSL, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem sp6ToSL6_statedSpMap (σ : F →+* F) (g : StatedSp 3 F) :
    sp6ToSL6 (statedSpMap σ 3 g) = SpecialLinearGroup.map σ (sp6ToSL6 g) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, coe_sp6ToSL6, coe_sp6ToSL6, mat_apply, mat_apply,
    coe_statedSpMap, coe_map_GL, RingHom.mapMatrix_apply, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_map]

end SL6

section Fixed

variable {F : Type} [Field F]

theorem sp6ToSL_mem_fixedSubgroup_iff {n : ℕ} (C : GL (Fin n) F)
    (g : SpecialLinearGroup (Fin n) F) :
    g ∈ fixedSubgroup
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F C *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n F) ↔
      (g : Matrix (Fin n) (Fin n) F)ᵀ * ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (g : Matrix (Fin n) (Fin n) F) = ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  set c : Matrix (Fin n) (Fin n) F := (C : Matrix (Fin n) (Fin n) F)
  set c' : Matrix (Fin n) (Fin n) F := ((C⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set G : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F)
  set G' : Matrix (Fin n) (Fin n) F :=
    ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hcc' : c * c' = 1 := by
    simp only [c, c']
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hc'c : c' * c = 1 := by
    simp only [c, c']
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGG' : G * G' = 1 := by
    simp only [G, G']
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hG'G : G' * G = 1 := by
    simp only [G, G']
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hfix : g ∈ fixedSubgroup
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F C *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n F) ↔
      c * G'ᵀ * c' = G := by
    change (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F C *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n F) g = g ↔ _
    rw [MulAut.mul_apply]
    constructor
    · intro h
      have h' := congrArg (fun x : SpecialLinearGroup (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h
      simpa only [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix] using h'
    · intro h
      apply Subtype.ext
      rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
      exact h
  rw [hfix]
  constructor
  · intro h
    calc Gᵀ * c' * G = Gᵀ * c' * (c * G'ᵀ * c') := by rw [h]
      _ = Gᵀ * (c' * c) * G'ᵀ * c' := by simp only [Matrix.mul_assoc]
      _ = (G' * G)ᵀ * c' := by rw [hc'c, Matrix.mul_one, Matrix.transpose_mul]
      _ = c' := by rw [hG'G, Matrix.transpose_one, Matrix.one_mul]
  · intro h
    calc c * G'ᵀ * c' = c * G'ᵀ * (Gᵀ * c' * G) := by rw [h]
      _ = c * (G * G')ᵀ * c' * G := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = G := by rw [hGG', Matrix.transpose_one, Matrix.mul_one, hcc', Matrix.one_mul]

theorem sp6ToSL_submatrix_blockSwapJ [CharP F 2] :
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :
        Matrix (Fin 6) (Fin 6) F).submatrix sp6ToSLIdx sp6ToSLIdx = fromBlocks 0 1 (-1) 0 := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [submatrix_apply, sp6ToSLIdx_inl, sp6ToSLIdx_inr,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ, of_apply, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      CharTwo.neg_eq, one_apply, Fin.val_castAdd, Fin.val_natAdd, Fin.ext_iff] <;>
    have := i.isLt <;> have := j.isLt <;> split_ifs <;> first | rfl | omega

theorem sp6ToSL_submatrix_gram_mul [CharP F 2] (G : Matrix (Fin 6) (Fin 6) F) :
    (Gᵀ * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 * G).submatrix
        sp6ToSLIdx sp6ToSLIdx =
      (G.submatrix sp6ToSLIdx sp6ToSLIdx)ᵀ * fromBlocks 0 1 (-1) 0 *
        G.submatrix sp6ToSLIdx sp6ToSLIdx := by
  rw [← sp6ToSL_submatrix_blockSwapJ, transpose_submatrix, submatrix_mul_equiv,
    submatrix_mul_equiv]

theorem sp6ToSL_submatrix_injective {R : Type*} {X Y : Matrix (Fin 6) (Fin 6) R}
    (h : X.submatrix sp6ToSLIdx sp6ToSLIdx = Y.submatrix sp6ToSLIdx sp6ToSLIdx) : X = Y := by
  have h' := congrArg (fun Z => Z.submatrix sp6ToSLIdx.symm sp6ToSLIdx.symm) h
  simpa only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] using h'

theorem sp6ToSL6_mem_range_iff [CharP F 2] (g : SpecialLinearGroup (Fin 6) F) :
    g ∈ (sp6ToSL6 (F := F)).range ↔
      (g : Matrix (Fin 6) (Fin 6) F)ᵀ *
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 *
            (g : Matrix (Fin 6) (Fin 6) F) =
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 := by
  constructor
  · rintro ⟨A, rfl⟩
    apply sp6ToSL_submatrix_injective
    have hA : (sp6ToSL6 A : Matrix (Fin 6) (Fin 6) F).submatrix sp6ToSLIdx sp6ToSLIdx =
        mat 3 F A := by
      rw [coe_sp6ToSL6, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, submatrix_submatrix,
        Equiv.symm_comp_self, submatrix_id_id]
    rw [sp6ToSL_submatrix_gram_mul, hA, sp6ToSL_submatrix_blockSwapJ]
    exact sp6ToSL_mat_symplectic A
  · intro h
    set M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
      (g : Matrix (Fin 6) (Fin 6) F).submatrix sp6ToSLIdx sp6ToSLIdx with hM
    have hdet : M.det = 1 := by
      rw [hM, det_submatrix_equiv_self, Matrix.SpecialLinearGroup.det_coe]
    have hsp : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0 := by
      rw [hM, ← sp6ToSL_submatrix_gram_mul, h, sp6ToSL_submatrix_blockSwapJ]
    have hmem : SpecialLinearGroup.toGL (⟨M, hdet⟩ : SpecialLinearGroup (Fin 3 ⊕ Fin 3) F) ∈
        StatedSp 3 F :=
      CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.2 hsp
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    change Matrix.reindexAlgEquiv F F sp6ToSLIdx M = _
    rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, hM, submatrix_submatrix,
      Equiv.self_comp_symm, submatrix_id_id]

theorem fixedSubgroup_graphGram6 [CharP F 2] :
    fixedSubgroup
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F
            (graphGram6 F) *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F) =
      (sp6ToSL6 (F := F)).range := by
  ext g
  rw [sp6ToSL_mem_fixedSubgroup_iff, coe_graphGram6_inv, sp6ToSL6_mem_range_iff]

end Fixed

section SL7

variable {F : Type} [Field F]

@[expose] noncomputable def sp6ToSLBlockMat (M : Matrix (Fin 6) (Fin 6) F) :
    Matrix (Fin 7) (Fin 7) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv (fromBlocks M 0 0 (1 : Matrix (Fin 1) (Fin 1) F))

theorem sp6ToSL_symm_six : (finSumFinEquiv.symm (6 : Fin 7) : Fin 6 ⊕ Fin 1) = Sum.inr 0 :=
  finSumFinEquiv_symm_last

@[simp] theorem sp6ToSLBlockMat_castSucc_castSucc (M : Matrix (Fin 6) (Fin 6) F) (i j : Fin 6) :
    sp6ToSLBlockMat M i.castSucc j.castSucc = M i j := by
  rw [sp6ToSLBlockMat, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_apply_castSucc, fromBlocks_apply₁₁]

@[simp] theorem sp6ToSLBlockMat_castSucc_six (M : Matrix (Fin 6) (Fin 6) F) (i : Fin 6) :
    sp6ToSLBlockMat M i.castSucc 6 = 0 := by
  rw [sp6ToSLBlockMat, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    finSumFinEquiv_symm_apply_castSucc, sp6ToSL_symm_six, fromBlocks_apply₁₂, Matrix.zero_apply]

@[simp] theorem sp6ToSLBlockMat_six_castSucc (M : Matrix (Fin 6) (Fin 6) F) (j : Fin 6) :
    sp6ToSLBlockMat M 6 j.castSucc = 0 := by
  rw [sp6ToSLBlockMat, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    finSumFinEquiv_symm_apply_castSucc, sp6ToSL_symm_six, fromBlocks_apply₂₁, Matrix.zero_apply]

@[simp] theorem sp6ToSLBlockMat_six_six (M : Matrix (Fin 6) (Fin 6) F) :
    sp6ToSLBlockMat M 6 6 = 1 := by
  rw [sp6ToSLBlockMat, Matrix.coe_reindexAlgEquiv, reindex_apply, submatrix_apply,
    sp6ToSL_symm_six, fromBlocks_apply₂₂, one_apply_eq]

theorem sp6ToSL_matrix_ext7 {R : Type*} {X Y : Matrix (Fin 7) (Fin 7) R}
    (h₁ : ∀ i j : Fin 6, X i.castSucc j.castSucc = Y i.castSucc j.castSucc)
    (h₂ : ∀ i : Fin 6, X i.castSucc 6 = Y i.castSucc 6)
    (h₃ : ∀ j : Fin 6, X 6 j.castSucc = Y 6 j.castSucc) (h₄ : X 6 6 = Y 6 6) : X = Y := by
  ext i j
  rcases Fin.eq_castSucc_or_eq_last (n := 6) i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last (n := 6) j with ⟨j, rfl⟩ | rfl
  exacts [h₁ i j, h₂ i, h₃ j, h₄]

theorem sp6ToSLBlockMat_mul (M N : Matrix (Fin 6) (Fin 6) F) :
    sp6ToSLBlockMat (M * N) = sp6ToSLBlockMat M * sp6ToSLBlockMat N := by
  rw [sp6ToSLBlockMat, sp6ToSLBlockMat, sp6ToSLBlockMat, ← map_mul, fromBlocks_multiply]
  simp

theorem sp6ToSLBlockMat_one : sp6ToSLBlockMat (1 : Matrix (Fin 6) (Fin 6) F) = 1 := by
  rw [sp6ToSLBlockMat, fromBlocks_one, map_one]

theorem sp6ToSLBlockMat_det (M : Matrix (Fin 6) (Fin 6) F) : (sp6ToSLBlockMat M).det = M.det := by
  rw [sp6ToSLBlockMat, Matrix.det_reindexAlgEquiv, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem sp6ToSLBlockMat_transpose (M : Matrix (Fin 6) (Fin 6) F) :
    (sp6ToSLBlockMat M)ᵀ = sp6ToSLBlockMat Mᵀ := by
  apply sp6ToSL_matrix_ext7 <;> simp

theorem sp6ToSLBlockMat_map (σ : F →+* F) (M : Matrix (Fin 6) (Fin 6) F) :
    (sp6ToSLBlockMat M).map σ = sp6ToSLBlockMat (M.map σ) := by
  apply sp6ToSL_matrix_ext7 <;> simp

theorem sp6ToSLBlockMat_injective : Function.Injective (sp6ToSLBlockMat (F := F)) := by
  intro M N h
  ext i j
  simpa using congrFun (congrFun h i.castSucc) j.castSucc

@[expose] noncomputable def sp6ToSLBlock :
    SpecialLinearGroup (Fin 6) F →* SpecialLinearGroup (Fin 7) F where
  toFun g := ⟨sp6ToSLBlockMat (g : Matrix (Fin 6) (Fin 6) F), by
    rw [sp6ToSLBlockMat_det, Matrix.SpecialLinearGroup.det_coe]⟩
  map_one' := Subtype.ext sp6ToSLBlockMat_one
  map_mul' _ _ := Subtype.ext (sp6ToSLBlockMat_mul _ _)

theorem coe_sp6ToSLBlock (g : SpecialLinearGroup (Fin 6) F) :
    (sp6ToSLBlock g : Matrix (Fin 7) (Fin 7) F) = sp6ToSLBlockMat (g : Matrix (Fin 6) (Fin 6) F) :=
  rfl

theorem sp6ToSLBlock_injective : Function.Injective (sp6ToSLBlock (F := F)) := fun _ _ hgh =>
  Subtype.ext (sp6ToSLBlockMat_injective (congrArg Subtype.val hgh))

@[expose] noncomputable def sp6ToSL7 : StatedSp 3 F →* SpecialLinearGroup (Fin 7) F :=
  sp6ToSLBlock.comp sp6ToSL6

theorem coe_sp6ToSL7 (A : StatedSp 3 F) :
    (sp6ToSL7 A : Matrix (Fin 7) (Fin 7) F) =
      sp6ToSLBlockMat (sp6ToSL6 A : Matrix (Fin 6) (Fin 6) F) :=
  rfl

theorem sp6ToSL7_injective : Function.Injective (sp6ToSL7 (F := F)) :=
  sp6ToSLBlock_injective.comp sp6ToSL6_injective

theorem sp6ToSLBlock_lin6Torus (t : Fin 3 → Fˣ) : sp6ToSLBlock (lin6Torus F t) = lin7Torus F t := by
  have hw : ∀ i : Fin 6, lin7Weights F t i.castSucc = lin6Weights F t i := by
    intro i
    fin_cases i <;> rfl
  have hl : lin7Weights F t 6 = 1 := rfl
  apply Subtype.ext
  rw [coe_sp6ToSLBlock, lin6Torus, lin7Torus, coe_diagTorusSL, coe_diagTorusSL]
  apply sp6ToSL_matrix_ext7
  · intro i j
    rw [sp6ToSLBlockMat_castSucc_castSucc]
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, diagonal_apply_eq, hw]
    · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ (fun h => hij (Fin.castSucc_injective _ h))]
  · intro i
    have hi : i.castSucc ≠ (6 : Fin 7) := Fin.castSucc_ne_last i
    rw [sp6ToSLBlockMat_castSucc_six, diagonal_apply_ne _ hi]
  · intro j
    have hj : (6 : Fin 7) ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
    rw [sp6ToSLBlockMat_six_castSucc, diagonal_apply_ne _ hj]
  · rw [sp6ToSLBlockMat_six_six, diagonal_apply_eq, hl, Units.val_one]

theorem sp6ToSL7_sp6Diag (t : Fin 3 → Fˣ) : sp6ToSL7 (sp6Diag F t) = lin7Torus F t := by
  rw [sp6ToSL7, MonoidHom.comp_apply, sp6ToSL6_sp6Diag, sp6ToSLBlock_lin6Torus]

theorem sp6ToSLBlock_map (σ : F →+* F) (g : SpecialLinearGroup (Fin 6) F) :
    sp6ToSLBlock (SpecialLinearGroup.map σ g) = SpecialLinearGroup.map σ (sp6ToSLBlock g) := by
  apply Subtype.ext
  rw [coe_sp6ToSLBlock, SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, coe_sp6ToSLBlock, sp6ToSLBlockMat_map]

theorem sp6ToSL7_statedSpMap (σ : F →+* F) (g : StatedSp 3 F) :
    sp6ToSL7 (statedSpMap σ 3 g) = SpecialLinearGroup.map σ (sp6ToSL7 g) := by
  rw [sp6ToSL7, MonoidHom.comp_apply, MonoidHom.comp_apply, sp6ToSL6_statedSpMap,
    sp6ToSLBlock_map]

end SL7

section Fixed7

variable {F : Type} [Field F]

theorem sp6ToSL_val_six : ((6 : Fin 7) : ℕ) = 6 := rfl

theorem sp6ToSL_gram7_eq :
    gram7 F =
      sp6ToSLBlockMat (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3) := by
  apply sp6ToSL_matrix_ext7
  · intro i j
    rw [sp6ToSLBlockMat_castSucc_castSucc]
    simp only [gram7, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ, of_apply,
      Fin.val_castSucc]
    have := i.isLt
    have := j.isLt
    split_ifs <;> first | rfl | omega
  · intro i
    rw [sp6ToSLBlockMat_castSucc_six]
    simp only [gram7, of_apply, Fin.val_castSucc, sp6ToSL_val_six]
    have := i.isLt
    split_ifs <;> first | rfl | omega
  · intro j
    rw [sp6ToSLBlockMat_six_castSucc]
    simp only [gram7, of_apply, Fin.val_castSucc, sp6ToSL_val_six]
    have := j.isLt
    split_ifs <;> first | rfl | omega
  · rw [sp6ToSLBlockMat_six_six]
    simp [gram7]

theorem sp6ToSL_gram7_castSucc (i : Fin 6) : gram7 F i.castSucc i.castSucc = 0 := by
  rw [sp6ToSL_gram7_eq, sp6ToSLBlockMat_castSucc_castSucc]
  simp only [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ, of_apply]
  split_ifs <;> first | rfl | omega

theorem sp6ToSL_gram7_six : gram7 F 6 6 = 1 := by
  rw [sp6ToSL_gram7_eq, sp6ToSLBlockMat_six_six]

@[expose] def sp6ToSLSwap7 : Fin 7 → Fin 7 := ![3, 4, 5, 0, 1, 2, 6]

theorem sp6ToSL_gram7_mul_apply (M : Matrix (Fin 7) (Fin 7) F) (k j : Fin 7) :
    (gram7 F * M) k j = M (sp6ToSLSwap7 k) j := by
  rw [mul_apply, Fin.sum_univ_seven]
  fin_cases k <;> simp [gram7, sp6ToSLSwap7]

theorem sp6ToSL_quad7 [CharP F 2] (M : Matrix (Fin 7) (Fin 7) F) (j : Fin 7) :
    (Mᵀ * gram7 F * M) j j = M 6 j ^ 2 := by
  rw [Matrix.mul_assoc, mul_apply, Fin.sum_univ_seven]
  simp only [transpose_apply, sp6ToSL_gram7_mul_apply]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  show M 0 j * M 3 j + M 1 j * M 4 j + M 2 j * M 5 j + M 3 j * M 0 j + M 4 j * M 1 j +
    M 5 j * M 2 j + M 6 j * M 6 j = M 6 j ^ 2
  linear_combination (M 0 j * M 3 j + M 1 j * M 4 j + M 2 j * M 5 j) * h2

theorem sp6ToSL_mul_transpose_eq {n : ℕ} {C G G' : Matrix (Fin n) (Fin n) F} (hCC : C * C = 1)
    (hGG' : G * G' = 1) (h : Gᵀ * C * G = C) : G * C * Gᵀ = C := by
  have h1 : C * Gᵀ * C = G' := by
    calc C * Gᵀ * C = C * Gᵀ * C * (G * G') := by rw [hGG', Matrix.mul_one]
      _ = C * (Gᵀ * C * G) * G' := by simp only [Matrix.mul_assoc]
      _ = G' := by rw [h, hCC, Matrix.one_mul]
  calc G * C * Gᵀ = G * C * Gᵀ * (C * C) := by rw [hCC, Matrix.mul_one]
    _ = G * (C * Gᵀ * C) * C := by simp only [Matrix.mul_assoc]
    _ = C := by rw [h1, hGG', Matrix.one_mul]

theorem sp6ToSL_eq_one_of_sq_eq_one [CharP F 2] {x : F} (h : x ^ 2 = 1) : x = 1 :=
  CharTwo.sq_injective (h.trans (one_pow 2).symm)

theorem sp6ToSL7_mem_range_iff [CharP F 2] (g : SpecialLinearGroup (Fin 7) F) :
    g ∈ (sp6ToSL7 (F := F)).range ↔
      (g : Matrix (Fin 7) (Fin 7) F)ᵀ * gram7 F * (g : Matrix (Fin 7) (Fin 7) F) = gram7 F := by
  constructor
  · rintro ⟨A, rfl⟩
    rw [coe_sp6ToSL7, sp6ToSLBlockMat_transpose, sp6ToSL_gram7_eq, ← sp6ToSLBlockMat_mul,
      ← sp6ToSLBlockMat_mul, (sp6ToSL6_mem_range_iff _).1 ⟨A, rfl⟩]
  · intro h
    set G : Matrix (Fin 7) (Fin 7) F := (g : Matrix (Fin 7) (Fin 7) F) with hGdef
    have hGG' : G * ((g⁻¹ : SpecialLinearGroup (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) = 1 := by
      rw [hGdef, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h' : G * gram7 F * Gᵀ = gram7 F := sp6ToSL_mul_transpose_eq (gram7_mul_self F) hGG' h
    have hrow : ∀ j : Fin 6, G 6 j.castSucc = 0 := fun j => by
      have hq := sp6ToSL_quad7 G j.castSucc
      rw [h, sp6ToSL_gram7_castSucc] at hq
      exact (pow_eq_zero_iff two_ne_zero).1 hq.symm
    have hcol : ∀ i : Fin 6, G i.castSucc 6 = 0 := fun i => by
      have hq := sp6ToSL_quad7 Gᵀ i.castSucc
      rw [transpose_transpose, h', transpose_apply, sp6ToSL_gram7_castSucc] at hq
      exact (pow_eq_zero_iff two_ne_zero).1 hq.symm
    have hcorner : G 6 6 = 1 := by
      have hq := sp6ToSL_quad7 G 6
      rw [h, sp6ToSL_gram7_six] at hq
      exact sp6ToSL_eq_one_of_sq_eq_one hq.symm
    set G₆ : Matrix (Fin 6) (Fin 6) F := G.submatrix Fin.castSucc Fin.castSucc with hG₆
    have hblk : G = sp6ToSLBlockMat G₆ := by
      apply sp6ToSL_matrix_ext7
      · intro i j
        rw [sp6ToSLBlockMat_castSucc_castSucc, hG₆, submatrix_apply]
      · intro i
        rw [sp6ToSLBlockMat_castSucc_six, hcol]
      · intro j
        rw [sp6ToSLBlockMat_six_castSucc, hrow]
      · rw [sp6ToSLBlockMat_six_six, hcorner]
    have hdet : G₆.det = 1 := by
      rw [← sp6ToSLBlockMat_det, ← hblk, hGdef, Matrix.SpecialLinearGroup.det_coe]
    have hsp : G₆ᵀ * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 * G₆ =
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 := by
      apply sp6ToSLBlockMat_injective
      rw [sp6ToSLBlockMat_mul, sp6ToSLBlockMat_mul, ← sp6ToSLBlockMat_transpose, ← hblk,
        ← sp6ToSL_gram7_eq, h]
    obtain ⟨A, hA⟩ := (sp6ToSL6_mem_range_iff ⟨G₆, hdet⟩).2 hsp
    refine ⟨A, Subtype.ext ?_⟩
    rw [coe_sp6ToSL7, hA]
    exact hblk.symm

theorem fixedSubgroup_graphGram7 [CharP F 2] :
    fixedSubgroup
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 7 F
            (graphGram7 F) *
          CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 7 F) =
      (sp6ToSL7 (F := F)).range := by
  ext g
  rw [sp6ToSL_mem_fixedSubgroup_iff, coe_graphGram7_inv, sp6ToSL7_mem_range_iff]

end Fixed7

end CFSG.SeitzReduction.F4Pilot
