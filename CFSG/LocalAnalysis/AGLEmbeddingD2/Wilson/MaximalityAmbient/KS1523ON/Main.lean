module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.Reduction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutCard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint.NativeSporadic

section Outer


set_option linter.unusedSectionVars false

theorem no_outer_fix_nine {G : Type} [Group G] (e : G ≃* ON) (τ : MulAut G)
    (hτ2 : τ ^ 2 = 1) (hτ : τ ∉ inner G) (E : Subgroup G) (hE : Nat.card E = 9)
    (hfix : ∀ g ∈ E, τ g = g) : False := by
  have hcard : Nat.card (CFSG.Sporadic.Schreier.fixSub τ) = 175560 :=
    CFSG.ComponentClassification.SolMax.card_fixSub_of_local
      CFSG.ComponentClassification.SolMax.ONOut.onOuterLocalInput_holds ⟨e⟩ τ
      (by rw [← sq]; exact hτ2) hτ
  have hle : E ≤ CFSG.Sporadic.Schreier.fixSub τ := fun g hg => hfix g hg
  have hdvd : Nat.card E ∣ Nat.card (CFSG.Sporadic.Schreier.fixSub τ) :=
    Subgroup.card_dvd_of_le hle
  rw [hE, hcard] at hdvd
  omega

theorem not_mem_inner_of {G : Type*} [Group G] {τ : MulAut G} (h : ¬ ∃ g : G, τ = MulAut.conj g) :
    τ ∉ inner G := fun ⟨g, hg⟩ => h ⟨g, hg.symm⟩

theorem no_outer_fix_nine_ON :
    ∀ τ : MulAut ON, τ ^ 2 = 1 → (¬ ∃ g : ON, τ = MulAut.conj g) →
      ∀ E : Subgroup ON, Nat.card E = 9 → (∀ g ∈ E, τ g = g) → False := by
  intro τ hτ2 hτ E hE hfix
  have h3 : τ ∉ inner ON := not_mem_inner_of hτ
  with_reducible_and_instances (exact no_outer_fix_nine (G := ON) (MulEquiv.refl _) τ hτ2 h3 E hE hfix)

end Outer

section Holds

set_option linter.unusedSectionVars false


theorem ks1523ONCent_holds : CFSG.RankThree.PartTwo.Sec15.KS1523ONCent :=
  ks1523ONCent_of_inputs
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank.card_le_eight_of_isElemAbelian_ON
    no_outer_fix_nine_ON

end Holds

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON
