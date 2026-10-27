module

public import CFSG.GH74.Generic.S1.Exo.ModelOps
public import CFSG.GH74.Generic.Front.DataLA

public section

namespace CFSG.GH74.Generic.S1.Exo

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

@[expose] def linZ0 (F : Type) [Field F] : ↥(StatedSL 4 F) :=
  ⟨⟨zDiag F, zDiag F, zDiag_mul_self, zDiag_mul_self⟩, by
    rw [statedSL_eq_detOne, mem_detOne]
    exact det_zDiag⟩

@[expose] def linNeg (F : Type) [Field F] : ↥(StatedSL 4 F) :=
  ⟨xGL F, by
    rw [statedSL_eq_detOne, mem_detOne, xGL_eq_neg_one, Units.val_neg, Units.val_one,
      Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
    norm_num⟩

@[expose] def linPerm02 (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

section Aux

variable {F : Type} [Field F]

theorem linPerm02_mul_self : linPerm02 F * linPerm02 F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linPerm02, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_linPerm02 : (linPerm02 F).det = 1 := by
  simp [linPerm02, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem linPerm02_mul_zDiag_mul_linPerm02 : linPerm02 F * zDiag F * linPerm02 F = -zDiag F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linPerm02, zDiag, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.diagonal_apply, Matrix.vecMul, dotProduct]

end Aux

@[expose] def linSwap (F : Type) [Field F] : ↥(StatedSL 4 F) :=
  ⟨⟨linPerm02 F, linPerm02 F, linPerm02_mul_self, linPerm02_mul_self⟩, by
    rw [statedSL_eq_detOne, mem_detOne]
    exact det_linPerm02⟩

section Facts

variable {F : Type} [Field F]

theorem coe_linZ0_matrix :
    (((linZ0 F : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![-1, -1, 1, 1] := rfl

theorem coe_linNeg : ((linNeg F : ↥(StatedSL 4 F)) : GL (Fin 4) F) = -1 := xGL_eq_neg_one

theorem coe_linNeg_matrix :
    (((linNeg F : ↥(StatedSL 4 F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by
  rw [coe_linNeg]
  simp

theorem linZ0_mul_self : linZ0 F * linZ0 F = 1 := Subtype.ext (Units.ext zDiag_mul_self)

theorem linNeg_mul_self : linNeg F * linNeg F = 1 := Subtype.ext xGL_mul_self

theorem linZ0_mem_blkLin : linZ0 F ∈ blkLin (F := F) 0 1 := isBlockAt_zDiag

theorem linZ0_comm (g : ↥(StatedSL 4 F)) (hg : g ∈ blkLin (F := F) 0 1) :
    g * linZ0 F = linZ0 F * g := by
  refine Subtype.ext (Units.ext ?_)
  show (((g : GL (Fin 4) F) * (linZ0 F : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    (((linZ0 F : GL (Fin 4) F) * (g : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  rw [Units.val_mul, Units.val_mul]
  exact IsBlockAt.comm_diagonal hg ![-1, -1, 1, 1] rfl

theorem linZ0_ne_one (h2 : (2 : F) ≠ 0) : linZ0 F ≠ 1 := by
  intro h
  have h' := congrArg (fun x : ↥(StatedSL 4 F) =>
    ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h
  simp only [coe_linZ0_matrix, Matrix.diagonal_apply_eq] at h'
  apply h2
  have h'' : (-1 : F) = 1 := by simpa using h'
  linear_combination -h''

theorem linNeg_ne_one (h2 : (2 : F) ≠ 0) : linNeg F ≠ 1 := by
  intro h
  have h' := congrArg (fun x : ↥(StatedSL 4 F) =>
    ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0) h
  simp only [coe_linNeg_matrix] at h'
  apply h2
  have h'' : (-1 : F) = 1 := by simpa using h'
  linear_combination -h''

theorem linSwap_conj : linSwap F * linZ0 F * (linSwap F)⁻¹ = linNeg F * linZ0 F := by
  have hs : (linSwap F)⁻¹ = linSwap F :=
    inv_eq_of_mul_eq_one_right (Subtype.ext (Units.ext linPerm02_mul_self))
  rw [hs]
  refine Subtype.ext (Units.ext ?_)
  show (((linSwap F : GL (Fin 4) F) * (linZ0 F : GL (Fin 4) F) * (linSwap F : GL (Fin 4) F) :
      GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    (((linNeg F : GL (Fin 4) F) * (linZ0 F : GL (Fin 4) F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_linNeg_matrix, neg_mul, one_mul]
  exact linPerm02_mul_zDiag_mul_linPerm02

end Facts

section Lin

variable {F : Type} [Field F] [Finite F]

theorem linBlk_quasisimple (hF : Nat.card F % 4 = 3) (h4 : 3 < Nat.card F) (a b : Fin 4)
    (hab : a ≠ b) : IsQuasisimple ↥((linBlockOps hF h4).blk a b) := by
  obtain ⟨e⟩ := lin_blk_equiv hF h4 a b hab
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl
      (Or.inr (by omega)) (Or.inr (by omega)))

theorem linNeg_center (hF : Nat.card F % 4 = 3) (g : ↥(StatedSL 4 F)) :
    g ∈ Subgroup.center ↥(StatedSL 4 F) ↔ g = 1 ∨ g = linNeg F := by
  rw [mem_center_statedSL_four_iff hF g]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)

theorem exists_conj_linZ0 (hF : Nat.card F % 4 = 3) (s : ↥(StatedSL 4 F)) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (hsn : s ≠ linNeg F) : ∃ P : ↥(StatedSL 4 F), P * s * P⁻¹ = linZ0 F := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
  set T : Matrix (Fin 4) (Fin 4) F := ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hT : T * T = 1 := by
    have := congrArg
      (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hs2
    simpa using this
  have hdet : T.det = 1 := by
    have : (s : GL (Fin 4) F) ∈ detOne F 4 := by
      rw [← statedSL_eq_detOne]
      exact s.2
    exact mem_detOne.1 this
  have h1 : T ≠ 1 := fun h => hs1 (Subtype.ext (Units.ext h))
  have hm1 : T ≠ -1 := fun h => hsn (Subtype.ext (Units.ext (by
    rw [coe_linNeg_matrix]
    exact h)))
  obtain ⟨P, hPdet, hTP⟩ := CFSG.GH74.Generic.exists_conj_diag4_det_one h2 T hT hdet h1 hm1
  let Pg : ↥(StatedSL 4 F) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P (by rw [hPdet]; exact one_ne_zero), by
      rw [statedSL_eq_detOne, mem_detOne]
      exact hPdet⟩
  have key : s * Pg = Pg * linZ0 F := Subtype.ext (Units.ext (by
    show T * P = P * Matrix.diagonal ![-1, -1, 1, 1]
    exact hTP))
  refine ⟨Pg⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, key, inv_mul_cancel_left]

end Lin

@[expose] noncomputable def linModelOps {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) : ModelOps (StatedSL 4 F) where
  ops := linBlockOps hF h4
  pf := linPairFacts hF h4
  blkq := linBlk_quasisimple hF h4
  qM := Nat.card F
  qM_odd := Nat.odd_iff.2 (by omega)
  blk_model a b hab := ⟨F, inferInstance, inferInstance, rfl, lin_blk_equiv hF h4 a b hab⟩
  z0 := linZ0 F
  z0_mem := linZ0_mem_blkLin
  z0_sq := linZ0_mul_self
  z0_ne := linZ0_ne_one (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega)))
  z0_cent := fun g hg => linZ0_comm g hg
  neg := linNeg F
  neg_center := linNeg_center hF
  neg_sq := linNeg_mul_self
  neg_ne := linNeg_ne_one (two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega)))
  norm := fun s hs2 hs1 hsn => exists_conj_linZ0 hF s hs2 hs1 hsn
  swap := ⟨linSwap F, linSwap_conj⟩

end CFSG.GH74.Generic.S1.Exo
