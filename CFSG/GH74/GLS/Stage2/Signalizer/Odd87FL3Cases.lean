module

public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Cases

variable {F : Type} [Field F] [Finite F]

theorem exists_conj_of_conjAut_sq {A : GL (Fin 3) F} (h : conjAut 3 F A * conjAut 3 F A = 1) :
    ∃ y : projectiveSL 3 F, conjAut 3 F A = MulAut.conj y := by
  have h1 : conjAut 3 F (A * A) * fieldAut 3 F 1 = 1 := by
    rw [map_one (fieldAut 3 F), mul_one, map_mul]
    exact h
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) (A * A) 1 h1
  have hscalM : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [smul_one_eq_diagonal]; rfl
  have hAA : (A : Matrix (Fin 3) (Fin 3) F) * A = (c : F) • 1 := by
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hc
    simp only [Units.val_mul] at this
    rw [← this, hscalM]
  obtain ⟨y, hy⟩ := conjAut_mem_inner_of_sq_scalar A c hAA
  exact ⟨y, hy.symm⟩

theorem linear3_involution_cases (h2 : (2 : F) ≠ 0) (α : MulAut (projectiveSL 3 F)) (hα : α * α = 1)
    (hne : α ≠ 1) :
    (∃ y : projectiveSL 3 F, y * y = 1 ∧ y ≠ 1 ∧ α = MulAut.conj y) ∨
    (∃ (A : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧ α = conjAut 3 F A * fieldAut 3 F σ) ∨
    (∃ B : GL (Fin 3) F, (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B ∧ α = conjAut 3 F B * dualAut 3 F) ∨
    (∃ (A : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 ∧
      α = conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) := by
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := 3) (by norm_num)).2 α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hαeq
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 3 F), mul_one] at hαeq
      left
      obtain ⟨y, hy⟩ := exists_conj_of_conjAut_sq (A := A) (by rw [← hαeq]; exact hα)
      have hyy : y * y = 1 := by
        have h1 : MulAut.conj (y * y) = (1 : MulAut (projectiveSL 3 F)) := by
          rw [map_mul, ← hy, ← hαeq]; exact hα
        have hc : y * y ∈ Subgroup.center (projectiveSL 3 F) := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ g) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc g * (y * y) = (y * y * g * (y * y)⁻¹) * (y * y) := by rw [this]
            _ = (y * y) * g := by group
        rw [center_projectiveSL_three_eq_bot (K := F), Subgroup.mem_bot] at hc
        exact hc
      refine ⟨y, hyy, fun hy1 => hne ?_, by rw [← hy]; exact hαeq⟩
      rw [hαeq, hy, hy1, map_one]
    · right; left; exact ⟨A, σ, hσ, hαeq⟩
  · rw [pow_one] at hαeq
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 3 F), mul_one] at hαeq
      right; right; left
      have hsq : (conjAut 3 F A * dualAut 3 F) ^ 2 = 1 := by rw [← hαeq, sq]; exact hα
      rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hsq with hA | hA
      · exact ⟨A, hA, hαeq⟩
      · exfalso
        have hdet := congrArg Matrix.det hA
        rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hdet
        have hu : IsUnit (A : Matrix (Fin 3) (Fin 3) F).det := Matrix.isUnits_det_units A
        have h5 : (2 : F) * (A : Matrix (Fin 3) (Fin 3) F).det = 0 := by
          have : (A : Matrix (Fin 3) (Fin 3) F).det = -(A : Matrix (Fin 3) (Fin 3) F).det := by
            have h5 : ((-1 : F) ^ 3) = -1 := by norm_num
            rw [h5] at hdet
            simpa using hdet
          linear_combination this
        rcases mul_eq_zero.1 h5 with h | h
        · exact h2 h
        · exact hu.ne_zero h
    · right; right; right; exact ⟨A, σ, hσ, hαeq⟩

omit [Finite F] in
theorem singleInv_projectiveSL_fl3 (h2 : (2 : F) ≠ 0) :
    CFSG.GH74.Generic.S3.SingleInv (projectiveSL 3 F) :=
  CFSG.GH74.Generic.S3.SingleInv.of_mulEquiv
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F)).symm)
    (CFSG.GH74.Generic.S3.singleInv_psl h2)

theorem exists_equiv_tInv {K : Type} [Group K] (h2 : (2 : F) ≠ 0) (e : K ≃* projectiveSL 3 F) {y : K}
    (hy2 : y * y = 1) (hy1 : y ≠ 1) : ∃ e' : K ≃* projectiveSL 3 F, e' y = tInv := by
  have hex2 : e y * e y = 1 := by rw [← map_mul, hy2, map_one]
  have hex1 : e y ≠ 1 := fun h => hy1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨g, hg⟩ := singleInv_projectiveSL_fl3 h2 (e y) tInv hex2 hex1 tInv_mul_self (tInv_ne_one h2)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  show MulAut.conj g (e y) = tInv
  rw [MulAut.conj_apply]
  exact hg

end Cases

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
