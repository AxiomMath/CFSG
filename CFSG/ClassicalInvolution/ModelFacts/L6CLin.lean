module

public import CFSG.ClassicalInvolution.ModelFacts.L6CInner
public import CFSG.ClassicalInvolution.ModelFacts.L6CGraph
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open scoped MatrixGroups

variable {F : Type} [Field F]

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) F

theorem eq_of_proj_eq (α α' : MulAut SL(4, F))
    (h : ∀ g, proj 4 F (α g) = proj 4 F (α' g)) : α = α' := by
  have hperf : Group.IsPerfect SL(4, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have hπk : (proj 4 F).ker ≤ Subgroup.center SL(4, F) := by
    rw [ker_proj, scalars_eq_center]
  have := UnitaryAut.hom_eq_of_central_ker_perfect hπk α.toMonoidHom α'.toMonoidHom h
  exact MulEquiv.ext fun g => DFunLike.congr_fun this g

theorem exists_sl_conj_rot4 (P : GL (Fin 4) F) :
    ∃ k : SL(4, F), k * rot4 F * k⁻¹ = slConjugation 4 F P (rot4 F) := by
  obtain ⟨k, hk⟩ := exists_sl_conj_block P
  exact ⟨k, hk MF15.rotJ⟩

variable [Finite F]

theorem lin4_exists_fixed (h2 : (2 : F) ≠ 0) (hn1 : ¬ IsSquare (-1 : F))
    (hσ : ∀ σ : F ≃+* F, σ * σ = 1 → σ = 1) (α : MulAut SL(4, F)) (hαα : α * α = 1) :
    ∃ k : SL(4, F), α (k * rot4 F * k⁻¹) = k * rot4 F * k⁻¹ := by
  have hφ2 : descendAut 4 F α * descendAut 4 F α = 1 := by
    rw [← map_mul, hαα, map_one]
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hform⟩ := hgen (descendAut 4 F α)
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hform
    have h1 := conjAut_mul_fieldAut_mul A A σ σ
    rw [← hform, hφ2] at h1
    obtain ⟨hσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1.symm
    have hσ1 := hσ σ hσσ
    subst hσ1
    have hAA : (A : 𝕄₄) * A = (c : F) • 1 := by
      have := congrArg (fun X : GL (Fin 4) F => (X : 𝕄₄)) hc
      simp at this
      rw [← this, Matrix.smul_one_eq_diagonal]
    have hαA : α = slConjugation 4 F A := by
      apply eq_of_proj_eq
      intro g
      calc proj 4 F (α g) = descendAut 4 F α (proj 4 F g) := (descendAut_proj 4 F α g).symm
        _ = (conjAut 4 F A * fieldAut 4 F 1) (proj 4 F g) := by rw [hform]
        _ = proj 4 F (slConjugation 4 F A g) := by rw [map_one, mul_one, conjAut_proj]
    obtain ⟨P, N, hAP, hNr⟩ := exists_inner hn1 h2 c.ne_zero hAA
    obtain ⟨k, hk⟩ := exists_sl_conj_rot4 P
    refine ⟨k, ?_⟩
    rw [hk, hαA]
    exact slConj_fixed_of_comm A P (rot4 F) N hAP hNr
  ·
    rw [pow_one] at hform
    have h1 := sq_conjAut_fieldAut_dualAut A σ
    rw [← hform, sq, hφ2] at h1
    obtain ⟨hσσ, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1.symm
    have hσ1 := hσ σ hσσ
    subst hσ1
    rw [map_one, mul_one] at hform
    have hα2 : (conjAut 4 F A * dualAut 4 F) ^ 2 = 1 := by rw [sq, ← hform]; exact hφ2
    have hαA : α = slConjugation 4 F A * slGraphAut 4 F := by
      apply eq_of_proj_eq
      intro g
      calc proj 4 F (α g) = descendAut 4 F α (proj 4 F g) := (descendAut_proj 4 F α g).symm
        _ = (conjAut 4 F A * dualAut 4 F) (proj 4 F g) := by rw [hform]
        _ = proj 4 F (slConjugation 4 F A ((g⁻¹).transpose)) := by
          rw [MulAut.mul_apply, dualAut_proj, conjAut_proj]
        _ = proj 4 F ((slConjugation 4 F A * slGraphAut 4 F) g) := rfl
    rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα2 with hs | hs
    · obtain ⟨P, hP⟩ := exists_graph_symm h2 A hs
      obtain ⟨k, hk⟩ := exists_sl_conj_rot4 P
      refine ⟨k, ?_⟩
      rw [hk, hαA, MulAut.mul_apply]
      exact slConj_transpose_inv_fixed A _ hP
    · obtain ⟨P, hP⟩ := exists_graph_alt h2 A hs
      obtain ⟨k, hk⟩ := exists_sl_conj_rot4 P
      refine ⟨k, ?_⟩
      rw [hk, hαA, MulAut.mul_apply]
      exact slConj_transpose_inv_fixed A _ hP

end CFSG.ClassicalInvolution.ModelFacts.L6C
