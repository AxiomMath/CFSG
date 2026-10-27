module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerGraphHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Inner

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem oddLieCentralQuotient_of_psl_involution {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSL n p f) (hm : Blueprint.LieModel J .PSL n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)} (hKc : IsComponent Kc) :
    OddLieCentralQuotient p Kc := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K), MulAut.congr e α = γ →
      (orderOf γ = 2 → ∀ (X : Type) [Group X], (X ≃* fixedSubgroup γ) →
        ∀ L : Subgroup X, IsComponent L → OddLieCentralQuotient p L) →
      OddLieCentralQuotient p Kc := by
    intro γ hγ h
    exact h (hγ ▸ hβ) _ ((fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) Kc hKc
  have hn : 2 ≤ n := hadm.2.2.1
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ →
      OddLieCentralQuotient p Kc := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact key _ hAσ fun hord X _ Ψ L hL => oddLieCentralQuotient_of_component_equiv Ψ
        (oddPSLInnerDiagInput n K p f hp hp2 hK hadm A hord) hL
    · exact key _ hAσ fun _ X _ Ψ L hL => odd_psl_field_oddLieCentralQuotient hn hp hp2 hf hK A
        σ hσ (hAσ ▸ hβ2) Ψ hL
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := psl_two_normal_form (MulAut.congr e α)
    exact hsemi A σ hAσ
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr e α))
    have hβ' : MulAut.congr e α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact hsemi A σ hβ'
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        exact key _ hβ' fun hord X _ Ψ L hL => oddLieCentralQuotient_of_component_equiv Ψ
          (oddPSLGraphInput_holds n K p f hp hp2 hK hn3 A hord) hL
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact key _ hβ' fun hord X _ Ψ L hL => odd_psl_graphField_oddLieCentralQuotient hn3 hp hp2
          hf hK A σ hσ hord Ψ hL

theorem oddLieCentralQuotient_of_E6_involution
    (hgraph : OddE6GraphInput) {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 n p f) (hm : Blueprint.LieModel J .E6 n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)} (hKc : IsComponent Kc) :
    OddLieCentralQuotient p Kc := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E6
    ((GH74.chevalleyExceptionalModel_of_lieModel (t := .E6) (by decide) hm).2 :
      UntwistedChevalleyModel J .E6 (p ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact odd_E6_explicit oddExcInnerDiagInput_E6 hgraph hp hp2 hadm.2.1 hF _ hβ
    (fixedSubgroupCongrEquiv e α) hKc

end CFSG.ComponentClassification.CatLeafProof
