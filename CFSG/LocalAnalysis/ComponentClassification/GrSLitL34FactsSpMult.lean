module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def SporadicMultTwoPartInput : Prop :=
  (∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q →
      Nonempty (Q ⧸ center Q ≃* Blueprint.NativeSporadic.J3) → Odd (Nat.card (center Q))) ∧
    ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q →
      Nonempty (Q ⧸ center Q ≃* Blueprint.NativeSporadic.ON) → Odd (Nat.card (center Q))

end CFSG.ComponentClassification.GSThmB
