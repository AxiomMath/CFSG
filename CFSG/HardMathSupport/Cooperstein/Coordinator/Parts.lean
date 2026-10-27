module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM InClassXBlock NineThreeTwo NineThreeThree
  NineThreeFour NineThreeFive NineThreeEight IsClassicalTwoOrG2)

@[expose] def Asc81bNineTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
      IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) ∨
        ∃ m : ℕ, 5 ≤ m ∧
          Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m))

@[expose] def Asc81bNineThreeAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → ∀ m : ℕ, (m = 7 ∨ 8 < m) →
    Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin m)) →
      InClassXBlock L ∨ (NineThreeFive X L ∧ IsA7FourType L) ∨ NineThreeSixNat X S L ∨
        NineThreeSevenNat X S L ∨ (NineThreeEight X S L ∧ IsTypeScriptL L)

end CFSG.HardMathSupport.Cooperstein.Coordinator
