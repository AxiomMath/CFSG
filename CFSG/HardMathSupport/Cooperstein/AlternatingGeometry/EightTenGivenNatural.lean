module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenNode

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19 CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM InClassXBlock NineThreeFive blockV)

@[expose] def EightTenOutcomes {G : Type} [Group G] (X S L : Subgroup G) : Prop :=
  InClassXBlock L ∨ (NineThreeFive (L ⊔ S) L ∧ IsA7FourType L) ∨
    (∃ n : ℕ, 5 ≤ n ∧ PairActionData (L ⊔ S) S L n ∧ NaturalSectionL S L (2 * n)) ∨
    (∃ n : ℕ, 3 ≤ n ∧ QuadBlockDataAct (L ⊔ S) S L n ∧ NaturalSectionL S L (4 * n)) ∨
    (∃ N r : ℕ, Even N ∧ 2 * r ≤ N ∧ 1 ≤ r ∧ 6 ≤ N - 2 * r ∧
      EightBlockData X S L r (N - 2 * r) ∧ IsShort2 L ∧ IsTypeScriptL L)

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
