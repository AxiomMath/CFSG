module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3GraphAut
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem kaL3_pow_semilinear [Finite F] {β : MulAut (projectiveSL 3 F)} {m : ℕ} (hm : Odd m)
    (hβ : β ^ m = 1) :
    ∃ (A : GL (Fin 3) F) (σ : F ≃+* F), β = conjAut 3 F A * fieldAut 3 F σ ∧ Odd (orderOf σ) := by
  obtain ⟨A, σ, rfl⟩ := exists_semilinear_of_odd_pow hm hβ
  refine ⟨A, σ, rfl, ?_⟩
  have h1 := CFSG.RankThree.LinearDescent.conjAut_mul_fieldAut_pow σ A m
  rw [h1] at hβ
  have hσm : σ ^ m = 1 := (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ hβ).1
  exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hσm)

theorem kaL3_aut_fixing_trivial [Finite F] {Ω : Subgroup SL(3, F)}
    (hlift : ∀ (A : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ g ∈ Ω, proj 3 F (semiSL A σ g) = proj 3 F g) → ∀ g ∈ Ω, semiSL A σ g = g)
    (hcomm : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ Ω, T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) →
        ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (htr : ∀ σ : F ≃+* F, Odd (orderOf σ) →
      (∀ g ∈ Ω, σ (Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) =
        Matrix.trace (g : Matrix (Fin 3) (Fin 3) F)) → σ = 1)
    {β : MulAut (projectiveSL 3 F)} {m : ℕ} (hm : Odd m) (hβ : β ^ m = 1)
    (hfix : ∀ g ∈ Ω, β (proj 3 F g) = proj 3 F g) : β = 1 := by
  obtain ⟨A, σ, rfl, hσodd⟩ := kaL3_pow_semilinear hm hβ
  have hf1 : ∀ g ∈ Ω, semiSL A σ g = g :=
    hlift A σ fun g hg => by rw [← beta_proj]; exact hfix g hg
  have hσ : σ = 1 := by
    refine htr σ hσodd fun g hg => ?_
    rw [← trace_semiSL A σ g, hf1 g hg]
  subst hσ
  have hAcomm : ∀ g ∈ Ω, (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * A := by
    intro g hg
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) (hf1 g hg)
    simp only [coe_semiSL] at h1
    have h2 : (g : Matrix (Fin 3) (Fin 3) F).map ⇑(1 : F ≃+* F) =
        (g : Matrix (Fin 3) (Fin 3) F) := by
      ext i j
      rfl
    rw [h2] at h1
    have h3 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)
        = (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
            ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
              (A : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.mul_assoc _ _ (A : Matrix (Fin 3) (Fin 3) F), h3, Matrix.mul_one]
      _ = (g : Matrix (Fin 3) (Fin 3) F) * A := by rw [h1]
  obtain ⟨c, hc⟩ := hcomm _ hAcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) A.mul_inv
    simp [hc] at this
  have hA : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) = A := by
    apply Units.ext
    rw [hc, smul_one_eq_diagonal]
    rfl
  rw [← hA, conjAut_scalar, map_one, mul_one]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
