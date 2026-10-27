module

public import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LocalAnalysis.SectionRank.QuasisimpleCatalog

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint

@[expose] def LargeReeCatalogHyp : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsStronglyQuasithin L →
    Odd (Nat.card (Subgroup.center L)) → ∀ f : ℕ,
    ReeTitsModel (L ⧸ Subgroup.center L) .twistedF4 2 f → CatalogStepConclusion L

@[expose] def TitsCatalogHyp : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsStronglyQuasithin L →
    Odd (Nat.card (Subgroup.center L)) → ∀ f : ℕ,
    ReeTitsModel (L ⧸ Subgroup.center L) .Tits 2 f → CatalogStepConclusion L

theorem catalog_exceptional_even_of
    (hree : LargeReeCatalogHyp) (htits : TitsCatalogHyp) :
    CatalogExceptionalEvenHyp := by
  intro L _ _ hL hSQT hodd f h
  rcases h with ⟨t, ht, hm⟩ | hm | hm | hm
  · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (catalog_g2_even hL hSQT hodd hm).2
    · exact absurd hm (higher_exceptional_even_central_quotient_exclusion hSQT _ le_rfl
        (Or.inl rfl))
    · exact absurd hm (higher_exceptional_even_central_quotient_exclusion hSQT _ le_rfl
        (Or.inr (Or.inl rfl)))
    · exact absurd hm (higher_exceptional_even_central_quotient_exclusion hSQT _ le_rfl
        (Or.inr (Or.inr (Or.inl rfl))))
    · exact absurd hm (higher_exceptional_even_central_quotient_exclusion hSQT _ le_rfl
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact absurd hm (higher_exceptional_even_central_quotient_exclusion hSQT _ le_rfl
        (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    · exact (catalog_triality_even hL hSQT hodd hm).2
  · exact hree L hL hSQT hodd f hm
  · exact htits L hL hSQT hodd f hm
  · exact catalog_suzuki hL hSQT hodd hm

end CFSG.SectionRank
