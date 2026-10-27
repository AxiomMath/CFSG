module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenPSpBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpNormal

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

namespace SevenList

variable {r : ℕ} {K : Type} [Field K]

theorem formJ_mul_formJ : formJ r K * formJ r K = -1 := by
  rw [formJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

variable (r K) in
@[expose] def formJSp : StatedSp r K :=
  ⟨⟨formJ r K, -formJ r K, by rw [Matrix.mul_neg, formJ_mul_formJ, neg_neg],
    by rw [Matrix.neg_mul, formJ_mul_formJ, neg_neg]⟩,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr (by
      change (formJ r K)ᵀ * formJ r K * formJ r K = formJ r K
      rw [ComponentClassification.Burgoyne.Sp.formJ_transpose, Matrix.neg_mul, formJ_mul_formJ,
        neg_neg, Matrix.one_mul])⟩

theorem stdSkew_mul_formJ :
    ComponentClassification.Burgoyne.Sp.stdSkew r K * formJ r K =
      -(formJ r K * ComponentClassification.Burgoyne.Sp.stdSkew r K) := by
  ext (i | i) (j | j) <;> by_cases hij : i = j <;>
    simp [ComponentClassification.Burgoyne.Sp.stdSkew, formJ, Matrix.diagonal, hij,
      Matrix.mul_apply]

open CFSG.ComponentClassification.Burgoyne.Sp (exists_skew_split_normal_form stdSkew) in
theorem exists_anticommute_of_skew_split (hr : 1 ≤ r) (hK : ringChar K ≠ 2) {A : gsp r K}
    {l : K} (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-(l ^ 2)) • formJ r K) :
    ∃ h : StatedSp r K, h⁻¹ * conjSp r K A h ∈ spScalars r K ∧ conjSp r K A h ≠ h := by
  obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK hl0 hAA hJ
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set Hm := ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hHm
  set Hi := (((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hHi
  have hHHi : Hm * Hi = 1 := (H : GL (Fin r ⊕ Fin r) K).mul_inv
  have hHiH : Hi * Hm = 1 := (H : GL (Fin r ⊕ Fin r) K).inv_mul
  have hHiH' : ∀ X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, Hi * (Hm * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hHiH, Matrix.one_mul]
  have hMe : M = Hm * (l • stdSkew r K) * Hi := by
    rw [← hH]
    calc M = (Hm * Hi) * M * (Hm * Hi) := by rw [hHHi, Matrix.one_mul, Matrix.mul_one]
      _ = Hm * (Hi * M * Hm) * Hi := by simp only [Matrix.mul_assoc]
  set h : StatedSp r K := H * formJSp r K * H⁻¹ with hh
  set P := ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hP
  have hhm : P = Hm * formJ r K * Hi := rfl
  have hkey : M * P = -(P * M) := by
    rw [hhm, hMe]
    calc Hm * (l • stdSkew r K) * Hi * (Hm * formJ r K * Hi) =
          l • (Hm * (stdSkew r K * formJ r K * Hi)) := by
          simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, hHiH']
      _ = -(Hm * formJ r K * Hi * (Hm * (l • stdSkew r K) * Hi)) := by
          rw [stdSkew_mul_formJ]
          simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, hHiH',
            Matrix.mul_neg, Matrix.neg_mul, smul_neg]
  set Pi := (((h⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hPi
  set Mi := (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have h1 : Pi * P = 1 := by
    rw [hPi, hP, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one]
  have h2 : M * Mi = 1 := (A : GL (Fin r ⊕ Fin r) K).mul_inv
  have hz : ((h⁻¹ * conjSp r K A h : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (-1) := by
    apply Units.ext
    have hlhs : (((h⁻¹ * conjSp r K A h : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = Pi * (M * P * Mi) := rfl
    rw [hlhs, hkey, GeneralLinearGroup.coe_scalar]
    calc Pi * (-(P * M) * Mi) = -((Pi * P) * (M * Mi)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = Matrix.scalar (Fin r ⊕ Fin r) ((-1 : Kˣ) : K) := by
          rw [h1, h2, Matrix.one_mul, Units.val_neg, Units.val_one, Matrix.scalar_apply,
            ← Matrix.diagonal_one, Matrix.diagonal_neg]
  refine ⟨h, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf, StatedScalars]
    exact ⟨-1, hz.symm⟩
  · intro heq
    rw [heq, inv_mul_cancel, Subgroup.coe_one] at hz
    have h3 := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl ⟨0, hr⟩) (Sum.inl ⟨0, hr⟩)) hz
    simp only [Units.val_one, Matrix.one_apply_eq, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Units.val_neg] at h3
    have h4 : (2 : K) = 0 := by
      calc (2 : K) = 1 + 1 := one_add_one_eq_two.symm
        _ = 1 + -1 := by rw [← h3]
        _ = 0 := add_neg_cancel 1
    exact Ring.two_ne_zero hK h4

open CFSG.ComponentClassification.Burgoyne.Sp (spCentEquiv) in
theorem card_fixed_conjAut_skew_split [Finite K] (hr : 1 ≤ r) (hK : ringChar K ≠ 2)
    {A : gsp r K} {l : K} (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (-(l ^ 2)) • formJ r K) :
    Nat.card (fixedSubgroup (conjAut r K A)) =
      Nat.card (LocalAnalysis.ComponentInitial.UnitaryHigher.similitudeCentralizer
        (LocalAnalysis.ComponentInitial.pairedSympForm K r)
        (Matrix.GeneralLinearGroup.toLin (A : GL (Fin r ⊕ Fin r) K))) := by
  obtain ⟨h, hhZ, hne⟩ := exists_anticommute_of_skew_split hr hK hl0 hAA hJ
  rw [card_fixed_conjAut_eq A hhZ hne]
  exact Nat.card_congr (spCentEquiv A).toEquiv

theorem card_generalLinearGroup_two_seven {W : Type} [Finite K] (hK : Nat.card K = 7)
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (hW : Module.finrank K W = 2) :
    Nat.card (LinearMap.GeneralLinearGroup K W) = 2016 := by
  have : Fintype K := Fintype.ofFinite K
  let b : Module.Basis (Fin 2) K W := Module.finBasisOfFinrankEq K W hW
  rw [Nat.card_congr (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv).toEquiv,
    Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK, Fin.prod_univ_two]
  norm_num

end SevenList

end CFSG.SeitzReduction.LinearPilot
