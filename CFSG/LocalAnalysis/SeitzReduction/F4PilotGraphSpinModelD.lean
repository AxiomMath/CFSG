module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelGen

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.RootSystem (roots)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

local instance f4PilotGraphSpinModelDNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem coe_spinMatrix_spinX_charTwo {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (he : toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (c : K) :
    ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 γ c) : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) = 1 + c • longMat K SpinPlus.plusIdx i j s t := by
  have hF := SpinPlus.isCoordFrame_plusFrame (K := K) three_le_rank_D4
  change ((spinMatrix (quadPlus 4 K) (rootElt (plusFrame 4 K three_le_rank_D4) (toStdD 4 γ) c) :
    GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) = _
  rw [coe_spinMatrix_rootElt hF, rootMat_eq hF hij he, repSign_cast_charTwo, one_smul]

theorem coe_spinMatrix_x_single_one (c : K) :
    ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (Pi.single 1 1) c) :
      GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inl 1) (.inl 2) 1 - single (.inr 2) (.inr 1) 1) :=
  coe_spinMatrix_spinX_charTwo (s := true) (t := false) (by decide) (by decide) c

theorem coe_spinMatrix_x_neg_single_one (c : K) :
    ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 1 1) c) :
      GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inr 1) (.inr 2) 1 - single (.inl 2) (.inl 1) 1) :=
  coe_spinMatrix_spinX_charTwo (i := 1) (j := 2) (s := false) (t := true) (by decide) (by decide) c

theorem coe_spinMatrix_x_single_two (c : K) :
    ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (Pi.single 2 1) c) :
      GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inl 2) (.inl 3) 1 - single (.inr 3) (.inr 2) 1) :=
  coe_spinMatrix_spinX_charTwo (s := true) (t := false) (by decide) (by decide) c

theorem coe_spinMatrix_x_single_three (c : K) :
    ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (Pi.single 3 1) c) :
      GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inl 2) (.inr 3) 1 - single (.inl 3) (.inr 2) 1) :=
  coe_spinMatrix_spinX_charTwo (i := 2) (j := 3) (s := true) (t := true) (by decide) (by decide) c

theorem coe_spinMatrix_x_neg_single_two (c : K) :
    ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 2 1) c) :
      GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inr 2) (.inr 3) 1 - single (.inl 3) (.inl 2) 1) :=
  coe_spinMatrix_spinX_charTwo (i := 2) (j := 3) (s := false) (t := true) (by decide) (by decide) c

theorem coe_spinMatrix_x_neg_single_three (c : K) :
    ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 3 1) c) :
      GL (Fin 4 ⊕ Fin 4) K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inr 2) (.inl 3) 1 - single (.inr 3) (.inl 2) 1) :=
  coe_spinMatrix_spinX_charTwo (i := 2) (j := 3) (s := false) (t := false) (by decide) (by decide)
    c

omit [CharP K 2] in
theorem one_add_smul_mul_one_add_smul_matrix {ι : Type} [Fintype ι] [DecidableEq ι] (c : K)
    (A B : Matrix ι ι K) :
    (1 + c • A) * (1 + c • B) = 1 + c • A + c • B + (c * c) • (A * B) := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
  abel

end Matrix

section Iota

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

theorem spinIota_eq_of_matrix {s : StatedSp 3 K} {y : spinGroup (quadPlus 4 K)}
    (hv : ((spinMatrix (quadPlus 4 K) y : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ omegaPlusVec K = omegaPlusVec K)
    (hres : ((spinMatrix (quadPlus 4 K) y : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).submatrix plusEmb plusEmb = mat 3 K s) :
    spinIota hK hf s = y := by
  rw [spinIota_apply, MulEquiv.symm_apply_eq]
  have hfix : spinOmegaEquiv y ∈ fixedSubgroup (omegaPlusBetaC K) :=
    (mem_fixedSubgroup_omegaPlusBetaC_iff K _).2 hv
  refine omegaPlusIota_eq_of_res hK hf (diagOmega_mem_omegaPlus8 K) (y := ⟨_, hfix⟩) ?_
  apply mat_injective
  rw [mat_apply, coe_omegaPlusRes]
  exact hres

theorem spinIota_x_single_one (c : K) :
    spinIota hK hf (Sp.x 3 K (Pi.single 1 1) c) =
      SpinPlus.x 4 K three_le_rank_D4 (Pi.single 1 1) c := by
  apply spinIota_eq_of_matrix
  · rw [coe_spinMatrix_x_single_one]
    simp only [add_mulVec, one_mulVec, smul_mulVec, sub_mulVec, single_mulVec_eq,
      omegaPlusVec_inl, omegaPlusVec_inr]
    simp
  · rw [coe_spinMatrix_x_single_one, mat_sp_x_single_one]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [plusEmb, one_apply]

theorem spinIota_x_neg_single_one (c : K) :
    spinIota hK hf (Sp.x 3 K (-Pi.single 1 1) c) =
      SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 1 1) c := by
  apply spinIota_eq_of_matrix
  · rw [coe_spinMatrix_x_neg_single_one]
    simp only [add_mulVec, one_mulVec, smul_mulVec, sub_mulVec, single_mulVec_eq,
      omegaPlusVec_inl, omegaPlusVec_inr]
    simp
  · rw [coe_spinMatrix_x_neg_single_one, mat_sp_x_neg_single_one]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [plusEmb, one_apply, CharTwo.neg_eq]

theorem spinIota_x_single_two_sq (c : K) :
    spinIota hK hf (Sp.x 3 K (Pi.single 2 1) (c ^ 2)) =
      SpinPlus.x 4 K three_le_rank_D4 (Pi.single 2 1) c *
        SpinPlus.x 4 K three_le_rank_D4 (Pi.single 3 1) c := by
  have hAB : ((single (.inl 2) (.inl 3) 1 - single (.inr 3) (.inr 2) 1 :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *
        (single (.inl 2) (.inr 3) 1 - single (.inl 3) (.inr 2) 1)) =
      -single (.inl 2) (.inr 2) 1 := by
    simp [sub_mul, mul_sub, single_mul_single_of_ne]
  have hM : ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (Pi.single 2 1) c *
      SpinPlus.x 4 K three_le_rank_D4 (Pi.single 3 1) c) : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inl 2) (.inl 3) 1 - single (.inr 3) (.inr 2) 1) +
        c • (single (.inl 2) (.inr 3) 1 - single (.inl 3) (.inr 2) 1) +
          (c * c) • -single (.inl 2) (.inr 2) 1 := by
    rw [map_mul, Units.val_mul, coe_spinMatrix_x_single_two, coe_spinMatrix_x_single_three,
      one_add_smul_mul_one_add_smul_matrix, hAB]
  apply spinIota_eq_of_matrix
  · rw [hM]
    simp only [add_mulVec, one_mulVec, smul_mulVec, sub_mulVec, neg_mulVec, single_mulVec_eq,
      omegaPlusVec_inl, omegaPlusVec_inr]
    simp only [ite_eq_right (show ¬((2 : Fin 4) = 3) by decide), mul_zero, zero_smul, sub_zero,
      neg_zero, smul_zero, add_zero]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  · rw [hM, mat_sp_x_single_two]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [plusEmb, one_apply, sq, CharTwo.neg_eq]

theorem spinIota_x_neg_single_two_sq (c : K) :
    spinIota hK hf (Sp.x 3 K (-Pi.single 2 1) (c ^ 2)) =
      SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 2 1) c *
        SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 3 1) c := by
  have hAB : ((single (.inr 2) (.inr 3) 1 - single (.inl 3) (.inl 2) 1 :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *
        (single (.inr 2) (.inl 3) 1 - single (.inr 3) (.inl 2) 1)) =
      -single (.inr 2) (.inl 2) 1 := by
    simp [sub_mul, mul_sub, single_mul_single_of_ne]
  have hM : ((spinMatrix (quadPlus 4 K) (SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 2 1) c *
      SpinPlus.x 4 K three_le_rank_D4 (-Pi.single 3 1) c) : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + c • (single (.inr 2) (.inr 3) 1 - single (.inl 3) (.inl 2) 1) +
        c • (single (.inr 2) (.inl 3) 1 - single (.inr 3) (.inl 2) 1) +
          (c * c) • -single (.inr 2) (.inl 2) 1 := by
    rw [map_mul, Units.val_mul, coe_spinMatrix_x_neg_single_two,
      coe_spinMatrix_x_neg_single_three, one_add_smul_mul_one_add_smul_matrix, hAB]
  apply spinIota_eq_of_matrix
  · rw [hM]
    simp only [add_mulVec, one_mulVec, smul_mulVec, sub_mulVec, neg_mulVec, single_mulVec_eq,
      omegaPlusVec_inl, omegaPlusVec_inr]
    simp only [ite_eq_right (show ¬((2 : Fin 4) = 3) by decide), mul_zero, zero_smul, sub_zero,
      neg_zero, smul_zero, add_zero]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  · rw [hM, mat_sp_x_neg_single_two]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [plusEmb, one_apply, sq, CharTwo.neg_eq]

end Iota

section Psi


variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

theorem spinToE6Sc_spinIota_x_single_one (c : K) :
    spinToE6Sc K (spinIota hK hf (Sp.x 3 K (Pi.single 1 1) c)) =
      e6Data_valid.xm K (Pi.single 3 1) c := by
  rw [spinIota_x_single_one, spinToE6Sc_x ((SpinPlus.Φ 4 K three_le_rank_D4).single_mem 1),
    d4Embed_single]
  rfl

theorem spinToE6Sc_spinIota_x_neg_single_one (c : K) :
    spinToE6Sc K (spinIota hK hf (Sp.x 3 K (-Pi.single 1 1) c)) =
      e6Data_valid.xm K (-Pi.single 3 1) c := by
  rw [spinIota_x_neg_single_one, spinToE6Sc_x ((SpinPlus.Φ 4 K three_le_rank_D4).neg_mem _
    ((SpinPlus.Φ 4 K three_le_rank_D4).single_mem 1)), d4Embed_neg_single]
  rfl

theorem spinToE6Sc_spinIota_x_single_two_sq (c : K) :
    spinToE6Sc K (spinIota hK hf (Sp.x 3 K (Pi.single 2 1) (c ^ 2))) =
      e6Data_valid.xm K (Pi.single 2 1) c * e6Data_valid.xm K (Pi.single 4 1) c := by
  rw [spinIota_x_single_two_sq, map_mul,
    spinToE6Sc_x ((SpinPlus.Φ 4 K three_le_rank_D4).single_mem 2),
    spinToE6Sc_x ((SpinPlus.Φ 4 K three_le_rank_D4).single_mem 3), d4Embed_single, d4Embed_single]
  rfl

theorem spinToE6Sc_spinIota_x_neg_single_two_sq (c : K) :
    spinToE6Sc K (spinIota hK hf (Sp.x 3 K (-Pi.single 2 1) (c ^ 2))) =
      e6Data_valid.xm K (-Pi.single 2 1) c * e6Data_valid.xm K (-Pi.single 4 1) c := by
  rw [spinIota_x_neg_single_two_sq, map_mul,
    spinToE6Sc_x ((SpinPlus.Φ 4 K three_le_rank_D4).neg_mem _
      ((SpinPlus.Φ 4 K three_le_rank_D4).single_mem 2)),
    spinToE6Sc_x ((SpinPlus.Φ 4 K three_le_rank_D4).neg_mem _
      ((SpinPlus.Φ 4 K three_le_rank_D4).single_mem 3)), d4Embed_neg_single, d4Embed_neg_single]
  rfl

end Psi

end CFSG.SeitzReduction.F4Pilot
