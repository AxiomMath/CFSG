module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLField
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLGF
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSLGraph

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof (nonempty_mulEquiv_psl_of_lieModel psl_two_normal_form)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBLinearSemilinear (semilinearAction)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.CatalogueBGraphField (graphFieldAction)

theorem u42_psl_concrete (hO : LieOrderFormulasInput) {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ f) (hadm : StatedLieAdmissible .PSL n 3 f)
    (σ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)) (hσ : orderOf σ = 2)
    {J : Subgroup ↥(fixedSubgroup σ)} (hJ : U42Hyp σ J) : False := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (τ : K ≃+* K), σ = semilinearAction n K A τ → False := by
    intro A τ hAτ
    by_cases hτ : τ = 1
    · subst hτ
      rw [CFSG.ComponentClassification.CatalogueBLinearSemilinear.semilinearAction_one_field]
        at hAτ
      subst hAτ
      exact u42_psl_inner hK hf hadm A hσ hJ
    · subst hAτ
      exact u42_psl_field hK hf hadm A τ hτ hσ hJ
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, τ, hAτ⟩ := psl_two_normal_form σ
    exact hsemi A τ hAτ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, τ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv n K).symm σ)
    have hβ' : σ = MulAut.congr (CFSG.ComponentClassification.CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K τ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one,
        CFSG.ComponentClassification.CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A τ hβ'
    · rw [pow_one] at hβ'
      by_cases hτ : τ = 1
      · subst hτ
        rw [map_one, mul_one,
          CFSG.ComponentClassification.CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        subst hβ'
        exact u42_psl_pureGraph hK hn3 hadm A hσ hJ
      · rw [CFSG.ComponentClassification.CatalogueBLinearHigherB.congr_graphField] at hβ'
        subst hβ'
        exact u42_psl_graphField hO hK hn3 hadm A τ hτ hσ hJ

theorem oddU42Free_PSL (hO : LieOrderFormulasInput) : OddU42Free .PSL := by
  apply oddU42Free_of_concrete
  intro S _ _ n f hadm hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  refine ⟨ProjectiveSpecialLinearGroup (Fin n) K, inferInstance, inferInstance, e, ?_⟩
  intro σ J hσ hJ
  exact u42_psl_concrete hO hK hadm σ hσ hJ

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
