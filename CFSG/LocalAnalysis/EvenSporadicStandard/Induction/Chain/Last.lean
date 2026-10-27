module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Repeat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

@[expose] def NoFiveAAbove (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H]
    (N : Subgroup H) : Prop :=
  Sol78Lit → Balance.UHered H → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    Hyp31 H N IsK IsL →
    Hyp31FourA H N IsK → ∀ K L J : Subgroup H, InL K → Maximal L →
      IsL ↥L → StdBare L → Lt K L → K ≤ L → IsK (↥K ⧸ CFSG.oddCore ↥K) → FiveALink K J → False

end CFSG.EvenSporadicStandard.Induction
