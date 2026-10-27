module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.Nodes
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ParabolicCase
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ClassicalRadical

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM IsClassicalTwoOrG2 NineThreeTwo InClassXBlock)

@[expose] def RadicalBarM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      CFSG.Quasithin.SmithC27.IsRadicalParabolic (barM X L)

theorem radicalBarM : RadicalBarM := by
  intro G _ _ X S L _ _ _ hc
  exact isRadicalParabolic_of_isClassicalTwoOrG2_center hc

@[expose] def EightNineNonParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      ¬ (Subgroup.normalizer (barM X (S ⊓ L) : Set _) ⊓ barM X L ≤
          Subgroup.normalizer (barM X S : Set _)) →
        InClassXBlock L ∨ SStarOrderTwo S L

theorem eightNine_of (hrad : RadicalBarM) (hbad : EightNineNonParabolic) : EightNine := by
  intro G _ _ X S L hX hA hL hc
  by_cases hY : Subgroup.normalizer (barM X (S ⊓ L) : Set _) ⊓ barM X L ≤
      Subgroup.normalizer (barM X S : Set _)
  · exact Or.inl (nineThreeTwo_of_isRadicalParabolic hA hL.toIsTwoPrimeComponent hc
      (hrad G X S L hX hA hL hc) hY)
  · rcases hbad G X S L hX hA hL hc hY with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem eightNine_of_nonParabolic
    (hbad : EightNineNonParabolic) : EightNine :=
  eightNine_of radicalBarM hbad

end CFSG.HardMathSupport.Cooperstein.StructureLie
