module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowSpinGraph

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame
open CFSG.LieType.Universal.Spin
open CFSG.LieType.RootSystem (roots)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)

@[expose] def flip3 (v : Fin 4 → ℤ) : Fin 4 → ℤ := ![v 0, v 1, v 2, -v 3]

theorem toStdD_d4Swap (v : Fin 4 → ℤ) : toStdD 4 (d4Swap v) = flip3 (toStdD 4 v) := by
  funext a
  fin_cases a
  all_goals simp [toStdD, d4Swap, flip3]
  ring

@[expose] def d4SignFlip (m : Fin 4) (r : Bool) : Bool := if m = 3 then !r else r

theorem flip3_single_add_single (i j : Fin 4) (s t : Bool) :
    flip3 (Pi.single i (boolSign s) + Pi.single j (boolSign t)) =
      Pi.single i (boolSign (d4SignFlip i s)) + Pi.single j (boolSign (d4SignFlip j t)) := by
  funext a
  fin_cases a <;> fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
    simp [flip3, d4SignFlip, boolSign]

@[expose] def plusSwap3 : Equiv.Perm (Fin 4 ⊕ Fin 4) := Equiv.swap (.inl 3) (.inr 3)

theorem plusSwap3_plusIdx (m : Fin 4) (r : Bool) :
    plusSwap3 (SpinPlus.plusIdx m r) = SpinPlus.plusIdx m (d4SignFlip m r) := by
  fin_cases m <;> cases r <;> rfl

variable {K : Type} [Field K]

@[expose] noncomputable def plusSwapMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  plusSwap3.toPEquiv.toMatrix

theorem plusSwapMat_mul_self : (plusSwapMat : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *
    plusSwapMat = 1 := by
  rw [plusSwapMat, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  have h : plusSwap3.trans plusSwap3 = Equiv.refl _ := Equiv.swap_swap _ _
  rw [h, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

@[expose] noncomputable def plusSwapGL : GL (Fin 4 ⊕ Fin 4) K :=
  ⟨plusSwapMat, plusSwapMat, plusSwapMat_mul_self, plusSwapMat_mul_self⟩

theorem plusSwapMat_mul_mul (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) :
    plusSwapMat * M * plusSwapMat = M.submatrix plusSwap3 plusSwap3 := by
  rw [plusSwapMat, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  have h : plusSwap3.symm = plusSwap3 := Equiv.symm_swap _ _
  rw [Matrix.submatrix_submatrix, h]
  rfl

theorem conj_longMat_plusSwap (i j : Fin 4) (s t : Bool) :
    plusSwapMat * longMat K SpinPlus.plusIdx i j s t * plusSwapMat =
      longMat K SpinPlus.plusIdx i j (d4SignFlip i s) (d4SignFlip j t) := by
  rw [plusSwapMat_mul_mul, longMat, longMat]
  rw [show ∀ A B : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K,
    (A - B).submatrix plusSwap3 plusSwap3 =
      A.submatrix plusSwap3 plusSwap3 - B.submatrix plusSwap3 plusSwap3 from fun _ _ => rfl]
  have h : plusSwap3.symm = plusSwap3 := Equiv.symm_swap _ _
  have hflip : ∀ (m : Fin 4) (r : Bool), d4SignFlip m (!r) = !d4SignFlip m r := by
    intro m r
    unfold d4SignFlip
    split_ifs <;> rfl
  rw [Matrix.submatrix_single_equiv, Matrix.submatrix_single_equiv, h, plusSwap3_plusIdx,
    plusSwap3_plusIdx, plusSwap3_plusIdx, plusSwap3_plusIdx, hflip, hflip]

section Main

variable [CharP K 2]

theorem repSign_cast_charTwo (i j : Fin 4) (s t : Bool) : ((repSign i j s t : ℤ) : K) = 1 := by
  unfold repSign boolSign
  split_ifs <;> simp [CharTwo.neg_eq]

theorem conj_rootMat_plusSwap {e : Fin 4 → ℤ} (he : IsLong e) :
    plusSwapMat * rootMat (K := K) (plusFrame 4 K three_le_rank_D4) e * plusSwapMat =
      rootMat (plusFrame 4 K three_le_rank_D4) (flip3 e) := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := he
  have hF := SpinPlus.isCoordFrame_plusFrame (K := K) three_le_rank_D4
  rw [rootMat_eq hF hij rfl, flip3_single_add_single, rootMat_eq hF hij rfl, Matrix.mul_smul,
    Matrix.smul_mul, conj_longMat_plusSwap, repSign_cast_charTwo, repSign_cast_charTwo]

variable
  [Finite K]

theorem spinMatrix_spinD4Graph (x : spinGroup (quadPlus 4 K)) :
    spinMatrix (quadPlus 4 K) (spinD4Graph K x) =
      plusSwapGL * spinMatrix (quadPlus 4 K) x * plusSwapGL⁻¹ := by
  have key : (spinMatrix (quadPlus 4 K)).comp (spinD4Graph K).toMonoidHom =
      (MulAut.conj plusSwapGL).toMonoidHom.comp (spinMatrix (quadPlus 4 K)) := by
    refine MonoidHom.eq_of_eqOn_dense closure_spinX_four_eq_top ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    apply Units.ext
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, spinD4Graph_x hγ, MulAut.conj_apply, Units.val_mul,
      Units.val_mul]
    change (spinMatrix (quadPlus 4 K) (rootElt (plusFrame 4 K three_le_rank_D4)
        (toStdD 4 (d4Swap γ)) c) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      plusSwapMat * (spinMatrix (quadPlus 4 K) (rootElt (plusFrame 4 K three_le_rank_D4)
        (toStdD 4 γ) c) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) * plusSwapMat
    have hF := SpinPlus.isCoordFrame_plusFrame (K := K) three_le_rank_D4
    rw [coe_spinMatrix_rootElt hF, coe_spinMatrix_rootElt hF, toStdD_d4Swap, mul_add, add_mul,
      mul_one, plusSwapMat_mul_self, Matrix.mul_smul, Matrix.smul_mul,
      conj_rootMat_plusSwap ((SpinPlus.isLong_toStdD_iff (by norm_num)).2 hγ)]
  exact DFunLike.congr_fun key x

@[expose] noncomputable def spinOmegaEquiv :
    spinGroup (quadPlus 4 K) ≃* StatedOmega (StatedQuadPlus 4 K) :=
  MulEquiv.ofBijective ((spinMatrix (quadPlus 4 K)).codRestrict _
      (spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus three_le_rank_D4)))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : spinMatrix (quadPlus 4 K) x = 1 := congrArg Subtype.val hx
      have hker : x ∈ (spinToStatedProj (quadPlus 4 K)
          (range_spinMatrix_quadPlus three_le_rank_D4)).ker := by
        rw [MonoidHom.mem_ker, spinToStatedProj_apply]
        have h1 : (⟨spinMatrix (quadPlus 4 K) x, spinMatrix_mem_of_range_eq _
            (range_spinMatrix_quadPlus three_le_rank_D4) x⟩ :
              StatedOmega (StatedQuadPlus 4 K)) = 1 := Subtype.ext hx'
        rw [h1]
        rfl
      rw [(spinToStatedProj_quadPlus (K := K) three_le_rank_D4).2.2,
        center_spinGroup_quadPlus_four_eq_bot] at hker
      exact hker,
    by
      rintro ⟨A, hA⟩
      rw [← range_spinMatrix_quadPlus three_le_rank_D4] at hA
      obtain ⟨x, rfl⟩ := hA
      exact ⟨x, rfl⟩⟩

omit
  [Finite K] in
theorem coe_spinOmegaEquiv (x : spinGroup (quadPlus 4 K)) :
    ((spinOmegaEquiv x : StatedOmega (StatedQuadPlus 4 K)) : GL (Fin 4 ⊕ Fin 4) K) =
      spinMatrix (quadPlus 4 K) x :=
  rfl

@[expose] noncomputable def plusSwapOmegaAut : MulAut (StatedOmega (StatedQuadPlus 4 K)) :=
  (spinOmegaEquiv.symm.trans (spinD4Graph K)).trans spinOmegaEquiv

theorem coe_plusSwapOmegaAut (A : StatedOmega (StatedQuadPlus 4 K)) :
    ((plusSwapOmegaAut A : StatedOmega (StatedQuadPlus 4 K)) : GL (Fin 4 ⊕ Fin 4) K) =
      plusSwapGL * (A : GL (Fin 4 ⊕ Fin 4) K) * plusSwapGL⁻¹ := by
  obtain ⟨x, rfl⟩ := spinOmegaEquiv.surjective A
  change ((spinOmegaEquiv (spinD4Graph K (spinOmegaEquiv.symm (spinOmegaEquiv x))) :
      StatedOmega (StatedQuadPlus 4 K)) : GL (Fin 4 ⊕ Fin 4) K) = _
  rw [MulEquiv.symm_apply_apply, coe_spinOmegaEquiv, coe_spinOmegaEquiv, spinMatrix_spinD4Graph]

theorem spinOmegaEquiv_spinD4Graph (x : spinGroup (quadPlus 4 K)) :
    spinOmegaEquiv (spinD4Graph K x) = plusSwapOmegaAut (spinOmegaEquiv x) := by
  change _ = spinOmegaEquiv (spinD4Graph K (spinOmegaEquiv.symm (spinOmegaEquiv x)))
  rw [MulEquiv.symm_apply_apply]

end Main

end CFSG.SeitzReduction.F4Pilot
