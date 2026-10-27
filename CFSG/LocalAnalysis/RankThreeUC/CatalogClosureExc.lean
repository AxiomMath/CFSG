module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcLarge
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcSmall
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcF4

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

@[expose] def ExceptionalTwoCase (G : Type) [Group G] : Prop :=
  (∃ (t : StatedLieTag) (f : ℕ), t ∈ chevalleyExceptionalTags ∧
      ChevalleyExceptionalModel G t 2 f) ∨
    (∃ (t : StatedLieTag) (f : ℕ), t ∈ reeTitsTags ∧ ReeTitsModel G t 2 f) ∨
    ∃ f : ℕ, SuzukiModel G 2 f

section Certified

set_option linter.unusedSectionVars false


theorem not_rankThreeUC_of_exceptionalTwoCase {G : Type} [Group G] [Finite G] (hS : Standing G)
    (h : ExceptionalTwoCase G) : ¬ rankThreeUC G := by
  rcases h with ⟨t, f, ht, hm⟩ | ⟨t, f, ht, hm⟩ | ⟨f, hm⟩
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (not_standing_of_smallExceptionalTwoCase hS (Or.inr (Or.inl ⟨f, hm⟩))).elim
    · by_cases hf : f = 1
      · exact not_rankThreeUC_of_F4Two hS hf hm
      · have hf2 : 2 ≤ f := by
          have := hm.1.2.1
          omega
        exact (not_standing_of_largeExceptionalTwoCase hS
          ⟨.F4, f, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf2⟩))), hm⟩).elim
    · exact (not_standing_of_largeExceptionalTwoCase hS
        ⟨.E6, f, Or.inl rfl, hm⟩).elim
    · exact (not_standing_of_largeExceptionalTwoCase hS
        ⟨.E7, f, Or.inr (Or.inl rfl), hm⟩).elim
    · exact (not_standing_of_largeExceptionalTwoCase hS
        ⟨.E8, f, Or.inr (Or.inr (Or.inl rfl)), hm⟩).elim
    · exact (not_standing_of_largeExceptionalTwoCase hS
        ⟨.twistedE6, f, Or.inr (Or.inr (Or.inr (Or.inl rfl))), hm⟩).elim
    · exact (not_standing_of_smallExceptionalTwoCase hS (Or.inr (Or.inr (Or.inl ⟨f, hm⟩)))).elim
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact absurd hm.1.2.2.2.1 (by decide)
    · exact (not_standing_of_smallExceptionalTwoCase hS
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hm⟩))))).elim
    · exact (not_standing_of_smallExceptionalTwoCase hS
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hm⟩))))).elim
  · exact (not_standing_of_smallExceptionalTwoCase hS (Or.inl ⟨f, hm⟩)).elim

end Certified

end CFSG.LocalAnalysis.RankThreeUC
