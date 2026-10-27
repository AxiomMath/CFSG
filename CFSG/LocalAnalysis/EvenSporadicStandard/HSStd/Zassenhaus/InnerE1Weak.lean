module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35HTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

@[expose] def KGHS3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Catalog S → IsSimpleGroup S →
    (Nat.card S).factorization 3 ≤ 4 → ∀ K : Subgroup S, CFSG.IsQuasisimple ↥K →
      IsSporadic (↥K ⧸ center ↥K) .HS → K = ⊤

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
