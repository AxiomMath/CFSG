module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.RankThree.PartOne.OutStructure

theorem noKlein_G2
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2) {Y : Type} [Group Y]
    (e : Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : NoKlein Y := by
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
  exact NoKlein.of_mulEquiv e.symm (noKlein_of_outPNice_two (outPNice_G2 Nat.prime_two hce))


end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
