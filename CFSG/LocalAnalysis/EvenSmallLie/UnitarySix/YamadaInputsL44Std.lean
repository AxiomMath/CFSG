module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSigma
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem center_SL_four_eq_bot [Finite F] (hF : Nat.card F = 4) : center SL(4, F) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  obtain ⟨c, hc4, hc⟩ := exists_scalar_of_mem_center hz
  have hc3 : (c : F) ^ 3 = 1 := pow_three_eq_one_of_card_four hF c.ne_zero
  have hc1 : (c : F) = 1 := by
    have h4 : (c : F) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc4, Units.val_one]
    have h := pow_succ (c : F) 3
    rw [h4, hc3, one_mul] at h
    exact h.symm
  rw [mem_bot]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [hc, hc1, Matrix.SpecialLinearGroup.coe_one, map_one]

variable (F) in
@[expose] def u₄Mat : Matrix (Fin 4) (Fin 4) F :=
  !![1, 1, 0, 0;
     0, 1, 1, 1;
     0, 0, 1, 1;
     0, 0, 0, 1]

theorem u₄Mat_upper : ∀ i j : Fin 4, j < i → u₄Mat F i j = 0 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [u₄Mat]

theorem u₄Mat_diag : ∀ i : Fin 4, u₄Mat F i i = 1 := by
  intro i
  fin_cases i <;> simp [u₄Mat]

theorem det_u₄Mat : (u₄Mat F).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => u₄Mat_upper i j h)]
  simp [u₄Mat_diag]

variable (F) in
@[expose] def u₄ : SL(4, F) := ⟨u₄Mat F, det_u₄Mat⟩

theorem u₄_mem_unitriangular : u₄ F ∈ unitriangular 4 F :=
  ⟨u₄Mat_upper, u₄Mat_diag⟩

theorem u₄_reg : ∀ i j : Fin 4, (j : ℕ) = i + 1 → (u₄ F : Matrix (Fin 4) (Fin 4) F) i j ≠ 0 := by
  intro i j h
  change u₄Mat F i j ≠ 0
  fin_cases i <;> fin_cases j <;> simp_all [u₄Mat]

theorem revGL_four_eq : (revGL 4 F : Matrix (Fin 4) (Fin 4) F) =
    !![0, 0, 0, 1;
       0, 0, 1, 0;
       0, 1, 0, 0;
       1, 0, 0, 0] := by
  ext i j
  rw [revGL_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem u₄_mem_msigma [Finite F] [CharP F 2] : u₄ F ∈ YamadaEnd.msigma F := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [msigma_eq_slUnitary, mem_slUnitary]
  change ((u₄Mat F).map _)ᵀ * _ * u₄Mat F = _
  have hmap : (u₄Mat F).map (frobeniusEquiv F 2 : F →+* F) = u₄Mat F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [u₄Mat]
  rw [hmap, revGL_four_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u₄Mat, Matrix.mul_apply, Fin.sum_univ_succ, h2]

variable (F) in
@[expose] def cJ : SL(4, F) ≃* SL(4, F) :=
  conjSL (YamadaEnd.antiDiag F) (YamadaEnd.antiDiag F) (YamadaEnd.antiDiag_mul_self F)

theorem coe_cJ (x : SL(4, F)) :
    (cJ F x : Matrix (Fin 4) (Fin 4) F) = YamadaEnd.antiDiag F * x * YamadaEnd.antiDiag F :=
  rfl

theorem cJ_transvection {i j : Fin 4} (h : i ≠ j) (c : F) :
    cJ F (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection (Fin.rev_injective.ne h) c :=
  YamadaEnd.conjSL_antiDiag_transvection F h c

theorem cJ_mem_msigma [Finite F] [CharP F 2] {x : SL(4, F)} (hx : x ∈ YamadaEnd.msigma F) :
    cJ F x ∈ YamadaEnd.msigma F := by
  rw [msigma_eq_slUnitary, mem_slUnitary] at hx ⊢
  rw [coe_cJ, ← revGL_four_eq_antiDiag, Matrix.map_mul, Matrix.map_mul, revGL_map,
    transpose_mul, transpose_mul, revGL_transpose]
  calc (revGL 4 F : Matrix (Fin 4) (Fin 4) F) *
        (((x : Matrix (Fin 4) (Fin 4) F).map (frobeniusEquiv F 2 : F →+* F))ᵀ *
          (revGL 4 F : Matrix (Fin 4) (Fin 4) F)) * (revGL 4 F : Matrix (Fin 4) (Fin 4) F) *
        ((revGL 4 F : Matrix (Fin 4) (Fin 4) F) * x * (revGL 4 F : Matrix (Fin 4) (Fin 4) F)) =
      (revGL 4 F : Matrix (Fin 4) (Fin 4) F) *
        (((x : Matrix (Fin 4) (Fin 4) F).map (frobeniusEquiv F 2 : F →+* F))ᵀ *
          (revGL 4 F : Matrix (Fin 4) (Fin 4) F) * x) * (revGL 4 F : Matrix (Fin 4) (Fin 4) F) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (revGL 4 F : Matrix (Fin 4) (Fin 4) F)
          (revGL 4 F : Matrix (Fin 4) (Fin 4) F), revGL_mul_self, Matrix.one_mul]
    _ = (revGL 4 F : Matrix (Fin 4) (Fin 4) F) := by
        rw [hx, revGL_mul_self, Matrix.one_mul]

theorem pstd_eq : (unitriangular 4 F).map (cJ F).toMonoidHom = YamadaEnd.pstd F := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    refine LinearCover.unitriangular_le_closure_rootElt.trans ((closure_le _).mpr ?_)
    rintro _ ⟨i, j, a, hij, rfl⟩
    change cJ F (LinearCover.rootElt i j a) ∈ YamadaEnd.pstd F
    rw [LinearCover.rootElt_of_ne hij.ne, cJ_transvection]
    exact subset_closure ⟨_, _, _, a, Fin.rev_lt_rev.mpr hij, rfl⟩
  · rw [YamadaEnd.pstd, closure_le]
    rintro _ ⟨i, j, h, c, hji, rfl⟩
    refine ⟨SpecialLinearGroup.transvection (Fin.rev_injective.ne h) c,
      transvection_mem_unitriangular (Fin.rev_lt_rev.mpr hji) c, ?_⟩
    change cJ F (SpecialLinearGroup.transvection (Fin.rev_injective.ne h) c) = _
    rw [cJ_transvection]
    exact Subtype.ext (by simp only [SpecialLinearGroup.transvection_coe, Fin.rev_rev])

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
