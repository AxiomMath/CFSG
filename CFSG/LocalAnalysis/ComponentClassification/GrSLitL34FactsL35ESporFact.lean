module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Rows

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris81Lemma35IdentSporFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G),
    L35.Config G p w v L K → ¬ N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K) →
    (Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .J2 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .HS) →
    L35.Concl p v L K

end CFSG.ComponentClassification.HarrisLit
