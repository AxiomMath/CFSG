module

public import CFSG.GH74.Generic.S1.Defs
public import CFSG.GH74.Generic.Front.DataLin

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def kron1 (X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![X 0 0, 0, X 0 1, 0; 0, X 0 0, 0, X 0 1; X 1 0, 0, X 1 1, 0; 0, X 1 0, 0, X 1 1]

@[expose] def skewK : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

@[expose] def hypK : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 0, 1; 0, 0, -1, 0; 0, -1, 0, 0; 1, 0, 0, 0]

@[expose] def compK (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, c, 0, 0; 1, 0, 0, 0; 0, 0, 0, c; 0, 0, 1, 0]

theorem kron1_one : kron1 (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kron1]

theorem kron1_mul (X Y : Matrix (Fin 2) (Fin 2) F) : kron1 (X * Y) = kron1 X * kron1 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron1, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem det_kron1 (X : Matrix (Fin 2) (Fin 2) F) : (kron1 X).det = X.det ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, kron1, Matrix.det_succ_row_zero, Fin.succAbove]
  ring

theorem kron1_neg_one : kron1 (-1 : Matrix (Fin 2) (Fin 2) F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kron1]

theorem kron1_skewK (X : Matrix (Fin 2) (Fin 2) F) (hX : X.det = 1) :
    kron1 X * skewK * (kron1 X)ᵀ = skewK := by
  rw [Matrix.det_fin_two] at hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron1, skewK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;>
    first | ring1 | linear_combination hX | linear_combination (-1 : F) * hX

theorem kron1_hypK (X : Matrix (Fin 2) (Fin 2) F) (hX : X.det = 1) :
    kron1 X * hypK * (kron1 X)ᵀ = hypK := by
  rw [Matrix.det_fin_two] at hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron1, hypK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;>
    first | ring1 | linear_combination hX | linear_combination (-1 : F) * hX

theorem kron1_compK (X : Matrix (Fin 2) (Fin 2) F) (c : F) :
    kron1 X * compK c = compK c * kron1 X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron1, compK, Matrix.mul_apply, Fin.sum_univ_four] <;> ring1

theorem hypK_transpose : (hypK : Matrix (Fin 4) (Fin 4) F)ᵀ = hypK := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypK]

theorem skewK_transpose : (skewK : Matrix (Fin 4) (Fin 4) F)ᵀ = -skewK := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewK]

theorem hypK_mul_self : (hypK : Matrix (Fin 4) (Fin 4) F) * hypK = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypK, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_hypK : (hypK : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, hypK, Matrix.det_succ_row_zero, Fin.succAbove]
  norm_num

theorem skewK_mul_self : (skewK : Matrix (Fin 4) (Fin 4) F) * skewK = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewK, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def kron1SL : SL(2, F) →* Matrix (Fin 4) (Fin 4) F where
  toFun X := kron1 (X : Matrix (Fin 2) (Fin 2) F)
  map_one' := kron1_one
  map_mul' _ _ := kron1_mul _ _

@[expose] def kronGL : SL(2, F) →* GL (Fin 4) F := kron1SL.toHomUnits

theorem coe_kronGL (X : SL(2, F)) :
    ((kronGL X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = kron1 (X : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem det_kronGL (X : SL(2, F)) :
    ((kronGL X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [coe_kronGL, det_kron1, X.2, one_pow]

theorem kronGL_neg_one : kronGL (-1 : SL(2, F)) = -1 := by
  apply Units.ext
  rw [coe_kronGL, Units.val_neg, Units.val_one]
  exact kron1_neg_one

@[expose] noncomputable def phiGL (P : GL (Fin 4) F) : SL(2, F) →* GL (Fin 4) F :=
  (MulAut.conj P).toMonoidHom.comp kronGL

theorem phiGL_apply (P : GL (Fin 4) F) (X : SL(2, F)) : phiGL P X = P * kronGL X * P⁻¹ := rfl

theorem phiGL_mem (P : GL (Fin 4) F) (X : SL(2, F)) : phiGL P X ∈ StatedSL 4 F := by
  rw [statedSL_eq_detOne, mem_detOne, ← Matrix.GeneralLinearGroup.val_det_apply, phiGL_apply, map_mul,
    map_mul, mul_comm (Matrix.GeneralLinearGroup.det P), mul_assoc, map_inv, mul_inv_cancel,
    mul_one, Matrix.GeneralLinearGroup.val_det_apply, det_kronGL]

@[expose] noncomputable def phiP (P : GL (Fin 4) F) : SL(2, F) →* ↥(StatedSL 4 F) :=
  (phiGL P).codRestrict (StatedSL 4 F) (phiGL_mem P)

theorem coe_phiP (P : GL (Fin 4) F) (X : SL(2, F)) :
    ((phiP P X : ↥(StatedSL 4 F)) : GL (Fin 4) F) = P * kronGL X * P⁻¹ := rfl

theorem neg_one_mem_range_phiP (P : GL (Fin 4) F) (z : ↥(StatedSL 4 F))
    (hz : (z : GL (Fin 4) F) = -1) : z ∈ (phiP P).range := by
  refine ⟨-1, Subtype.ext ?_⟩
  rw [coe_phiP, kronGL_neg_one, hz, mul_neg, mul_one, neg_mul, mul_inv_cancel]

theorem goodSub_range_phiP [Finite F] (hF : Nat.card F % 4 = 3) (P : GL (Fin 4) F) :
    GoodSub (Nat.card F = 3) (phiP P).range := by
  by_cases h4 : 4 ≤ Nat.card F
  · left
    have hSL : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
    exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)
  · right
    have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
    have h3 : Nat.card F = 3 := by omega
    refine ⟨?_, h3⟩
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 (fun g hg => hg.1)
    · set S : Set ↥(StatedSL 4 F) := {g | g ∈ (phiP P).range ∧ Odd (orderOf g)} with hS
      rintro _ ⟨X, rfl⟩
      exact map_mem_closure_of_elementary (phiP P) S
        (fun e he => ⟨⟨e, rfl⟩, odd_orderOf_map_elementary hodd (phiP P) he⟩) X

theorem goodFixedCentral_of_phiP [Finite F] (hF : Nat.card F % 4 = 3)
    (α : MulAut ↥(StatedSL 4 F)) (P : GL (Fin 4) F)
    (hfix : ∀ X : SL(2, F),
      ((α (phiP P X) : ↥(StatedSL 4 F)) : GL (Fin 4) F) = P * kronGL X * P⁻¹) :
    GoodFixedCentral (Nat.card F = 3) α := by
  refine ⟨(phiP P).range, ?_, ?_, goodSub_range_phiP hF P⟩
  · rintro _ ⟨X, rfl⟩
    exact Subtype.ext (hfix X)
  · intro z hz
    rcases (mem_center_statedSL_four_iff hF z).1 hz with h | h
    · have : z = 1 := Subtype.ext h
      rw [this]
      exact one_mem _
    · exact neg_one_mem_range_phiP P z (by rw [h, xGL_eq_neg_one])

end CFSG.GH74.Generic.S1
