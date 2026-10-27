module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankE7
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section E7


theorem crossRankE7SevenSplit_holds : CrossRankE7SevenSplit := by
  intro q hv h7
  refine ExcRank.crossRankAtPrime_of_model fun hp hp5 hdp => ?_
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    (GaloisField q.p q.exponent) hK
  haveI : Finite (adjointGroup Tag.E7 (GaloisField q.p q.exponent)) :=
    generated_group_finite Tag.E7 _
  refine ⟨adjointGroup Tag.E7 (GaloisField q.p q.exponent), inferInstance, inferInstance,
    ⟨φ.symm.trans (adjointQuotientEquiv Tag.E7 _)⟩, fun y hy => ?_⟩
  have := ExcRank.e7_seven_centralizer_rank (GaloisField q.p q.exponent) (by rw [hK]; exact h7) y hy
  omega

end E7

end CFSG.LocalAnalysis.RankFourTheoremC
