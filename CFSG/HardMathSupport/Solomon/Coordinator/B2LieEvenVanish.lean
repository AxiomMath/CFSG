module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueEvenExceptionalCheck

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatalogueU
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedClassicalModel StatedLieTag)

theorem evenExceptional_oddCore_eq_bot
    {X : Type} [Group X] [Finite X] [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {f : ℕ}
    (hmodel : ChevalleyExceptionalModel (CFSG.generalizedFitting X) t 2 f) {z : X}
    (hz2 : orderOf z = 2) : CFSG.oddCore ↥(centralizer ({z} : Set X)) = ⊥ := by
  have hE6 := evenE6OuterInvolutionInput_holds
  obtain ⟨hadm, hcase⟩ := hmodel
  have hf : 1 ≤ f := hadm.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_almost_simple_odd_core_vanishing
      hnonab ⟨hadm, hcase⟩).2 z hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab
      (e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inl rfl) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab
      (e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inl rfl)) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab
      (e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inl rfl))) hf K hK) hz2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab
      (e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv _ K))
      (adjointGroup_involution_centralizer_oddCore hE6 (.inr (.inr (.inr rfl))) hf K hK) hz2
  all_goals
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hcase
    obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
      ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
        RingHom.ext fun _ => rfl⟩
    obtain ⟨e'⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv _
      Nat.prime_two hf K hK _ hσ
    exact oddCore_centralizer_eq_bot_of_conjModel hnonab (e.trans e')
      (graphFixedRootGroup_involution_centralizer_oddCore hE6 _ hf K hK σ' hσ) hz2

end CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt
