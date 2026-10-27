module

public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutGen
public import CFSG.RankThree.PartOne.S11d.OutExceptional

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open TauCeti CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof CFSG.RankThree.PartOne.OutStructure
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut (outTwoCyclic_of_outPNice_two)

set_option linter.unusedSectionVars false


theorem outTwoCyclic_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) (hp2 : q.p = 2)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* (CFSGIndex.lie ⟨.F4 q, hv⟩).Group) :
    OutTwoCyclic Y := by
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel Y .F4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hp2 e⟩
  rw [hp2] at hce
  exact outTwoCyclic_of_outPNice_two (outPNice_F4 Nat.prime_two hce)

theorem outTwoCyclic_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) (hp2 : q.p = 2)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* (CFSGIndex.lie ⟨.E7 q, hv⟩).Group) :
    OutTwoCyclic Y := by
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel Y .E7 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv hp2 e⟩
  rw [hp2] at hce
  exact outTwoCyclic_of_outPNice_two (outPNice_E7 Nat.prime_two hce)

theorem outTwoCyclic_E8 (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (hp2 : q.p = 2)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* (CFSGIndex.lie ⟨.E8 q, hv⟩).Group) :
    OutTwoCyclic Y := by
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel Y .E8 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hp2 e⟩
  rw [hp2] at hce
  exact outTwoCyclic_of_outPNice_two (outPNice_E8 Nat.prime_two hce)

theorem outTwoCyclic_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (hp2 : q.p = 2) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) : OutTwoCyclic Y := by
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel Y .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hp2 (by decide) e⟩
  rw [hp2] at hce
  exact outTwoCyclic_of_outPNice_two (outPNice_twistedE6 Nat.prime_two (by norm_num) hce)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
