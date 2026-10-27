module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineReduction

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM IsClassicalTwoOrG2 Asc81bEightFive InClassXBlock)
open CFSG.QuasithinUnique (IsSylowTwoOf)

@[expose] def EightNineBotCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      barM X (S ⊓ L) = ⊥ → SStarOrderTwo S L

@[expose] def EightNineNeCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      barM X (S ⊓ L) ≠ ⊥ → ¬ IsSylowTwoOf (S ⊓ L) L →
        Subgroup.normalizer (barM X (S ⊓ L) : Set _) ⊓ barM X L ≤
          Subgroup.normalizer (barM X S : Set _)

theorem eightNineNonParabolic_of_split (h85 : Asc81bEightFive) (hbot : EightNineBotCase)
    (hne : EightNineNeCase) : EightNineNonParabolic := by
  intro G _ _ X S L hX hA hL hc hY
  by_cases hSyl : IsSylowTwoOf (S ⊓ L) L
  · exact Or.inl (h85 G X S L hX hA hL.toIsTwoPrimeComponent hSyl)
  · by_cases h : barM X (S ⊓ L) = ⊥
    · exact Or.inr (hbot G X S L hX hA hL hc h)
    · exact (hY (hne G X S L hX hA hL hc h hSyl)).elim

end CFSG.HardMathSupport.Cooperstein.StructureLie
