module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutCModel

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
  CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
open scoped MatrixGroups

section Core

variable {F : Type} [Field F]

theorem exists_scalar_of_proj_eq (A : GL (Fin 3) F) (x y a' b' : F)
    (h : proj 3 F (CatalogueBHigherLinearAction.slConjugation 3 F A (elM x y)) =
      proj 3 F (elP a' b')) :
    ∃ c : F, ((elP a' b' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      c • ((A : Matrix (Fin 3) (Fin 3) F) * ((elM x y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) := by
  set S : SL(3, F) := CatalogueBHigherLinearAction.slConjugation 3 F A (elM x y) with hS
  have hs : S⁻¹ * elP a' b' ∈ scalars 3 F := proj_eq_proj_iff.mp h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hs
  refine ⟨(c : F), ?_⟩
  have hN : ((elP a' b' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (S : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F) := by
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F))
      (show S * (S⁻¹ * elP a' b') = elP a' b' by group)
    rw [Matrix.SpecialLinearGroup.coe_mul S (S⁻¹ * elP a' b'), hc] at h1
    exact h1.symm
  have hSm : (S : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * ((elM x y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hS]
    exact CatalogueBHigherLinearAction.slConjugation_matrix 3 F A (elM x y)
  have hAiA : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := Units.inv_mul A
  have hsc : Matrix.scalar (Fin 3) (c : F) = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hN, hSm, hsc]
  calc (A : Matrix (Fin 3) (Fin 3) F) * ((elM x y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((c : F) • 1) * (A : Matrix (Fin 3) (Fin 3) F)
      = (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
          ((elM x y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F))) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F)]
    _ = (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
          ((elM x y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) := by rw [hAiA, Matrix.mul_one]

theorem entries_of_scalar_elP (A : Matrix (Fin 3) (Fin 3) F) (x y a' b' c : F)
    (h : ((elP a' b' : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * A =
      c • (A * ((elM x y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))) :
    (c ≠ 1 → A 0 0 = 0 ∧ A 1 0 = 0 ∧ A 0 1 = 0 ∧ A 1 1 = 0) ∧
      (c = 1 → x * A 0 0 + y * A 0 1 = 0 ∧ x * A 1 0 + y * A 1 1 = 0) := by
  have e00 := congrFun (congrFun h 0) 0
  have e10 := congrFun (congrFun h 1) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, coe_elP, coe_elM] at e00 e10 e01 e11 e02 e12
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hc' : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (mul_eq_zero.mp (by linear_combination e00 : (1 - c) * A 0 0 = 0)).resolve_left hc'
    · exact (mul_eq_zero.mp (by linear_combination e10 : (1 - c) * A 1 0 = 0)).resolve_left hc'
    · exact (mul_eq_zero.mp (by linear_combination e01 : (1 - c) * A 0 1 = 0)).resolve_left hc'
    · exact (mul_eq_zero.mp (by linear_combination e11 : (1 - c) * A 1 1 = 0)).resolve_left hc'
  · subst hc
    refine ⟨?_, ?_⟩
    · linear_combination -e02
    · linear_combination -e12

theorem det_eq_zero_of_scalar_instances (A : Matrix (Fin 3) (Fin 3) F) (c₁ c₂ a₁ b₁ a₂ b₂ : F)
    (h₁ : ((elP a₁ b₁ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * A =
      c₁ • (A * ((elM (-1) 0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)))
    (h₂ : ((elP a₂ b₂ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * A =
      c₂ • (A * ((elM 0 (-1) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))) : A.det = 0 := by
  obtain ⟨k₁, l₁⟩ := entries_of_scalar_elP A _ _ _ _ _ h₁
  obtain ⟨k₂, l₂⟩ := entries_of_scalar_elP A _ _ _ _ _ h₂
  have h4 : A 0 0 = 0 ∧ A 1 0 = 0 ∧ A 0 1 = 0 ∧ A 1 1 = 0 := by
    by_cases hc₁ : c₁ = 1
    · by_cases hc₂ : c₂ = 1
      · obtain ⟨u1, u2⟩ := l₁ hc₁
        obtain ⟨v1, v2⟩ := l₂ hc₂
        refine ⟨?_, ?_, ?_, ?_⟩
        · linear_combination -u1
        · linear_combination -u2
        · linear_combination -v1
        · linear_combination -v2
      · exact k₂ hc₂
    · exact k₁ hc₁
  obtain ⟨z00, z10, z01, z11⟩ := h4
  rw [Matrix.det_fin_three]
  simp [z00, z10, z01, z11]

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
