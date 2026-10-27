module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

@[expose] def KFactThreeRankOneSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ i : TauCeti.CFSGIndex, Nonempty (S ≃* i.Group) →
      CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1 →
      (∃ d : TauCeti.ValidLieTypeIndex,
          ((∃ q : TauCeti.PrimePower, q.p ≠ 3 ∧ d.1 = .A 1 q) ∨
            (∃ q : TauCeti.PrimePower, q.card % 3 = 2 ∧ d.1 = .A 2 q) ∨
            (∃ q : TauCeti.PrimePower, q.card % 3 = 1 ∧ d.1 = .twistedA 2 q)) ∧
          Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
        Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) ∨
        Nonempty (S ≃* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
