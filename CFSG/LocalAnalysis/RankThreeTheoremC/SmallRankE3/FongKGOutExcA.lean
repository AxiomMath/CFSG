module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutGen
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.Adapters.TauCetiExceptional.EvenB1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

open TauCeti CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof CFSG.RankThree.PartOne.OutStructure

theorem outTwoCyclic_G2
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2) {Y : Type} [Group Y]
    [Finite Y] (e : Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : OutTwoCyclic Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField q.p q.exponent) hK
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, ?_, ⟨e0.symm⟩⟩
    · rw [← PrimePower.card_def]
      exact hq3
    · rw [hK, PrimePower.card_def]
  rw [hp2] at hce
  exact outTwoCyclic_of_outPNice_two (OutPNice.of_mulEquiv e (outPNice_G2 Nat.prime_two hce))

theorem outTwoCyclic_trialityD4
    (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid) (hp2 : q.p = 2) {Y : Type} [Group Y]
    [Finite Y] (e : Y ≃* (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) : OutTwoCyclic Y := by
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel Y .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hp2 (by decide) e⟩
  rw [hp2] at hce
  exact outTwoCyclic_of_outPNice_two (outPNice_trialityD4 Nat.prime_two hce)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut
