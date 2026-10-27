module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus

@[expose] def MonsterHopfTrivial : Prop :=
  Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
    (CFSG.RankThree.PartTwo.Sec4.Spor .M)) = 1

theorem MonsterHopfTrivial.of_sporadicMultipliers
    (h : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : MonsterHopfTrivial :=
  h.1 .M

section MonsterHopfTrivialHolds

theorem monsterHopfTrivial_holds : MonsterHopfTrivial :=
  MonsterHopfTrivial.of_sporadicMultipliers
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

end MonsterHopfTrivialHolds

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
