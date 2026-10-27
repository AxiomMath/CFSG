module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporMData
import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicBMData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.RankThree.PartOne.StrongP

theorem wcSporadicAt_M_of_data [Finite (Carrier .M)]
    (hcard : Nat.card (Carrier .M) = monsterOrder)
    (h3 : HasNoncommPair 3 (Carrier .M)) (h5 : HasNoncommPair 5 (Carrier .M))
    (h7 : HasNoncommPair 7 (Carrier .M)) (h13 : HasNoncommPair 13 (Carrier .M))
    (h11 : WCOn 11 (Carrier .M)) : WCSporadicAt .M := by
  have hN : Nat.card (Carrier .M) = 808017424794512875886459904961710757005754368000000000 :=
    hcard.trans (by norm_num [monsterOrder])
  refine wcSporadicAt_of_card .M (N := 808017424794512875886459904961710757005754368000000000) hN ?_
  intro q hq hq2 hdvd
  have hpf : Nat.primeFactors 808017424794512875886459904961710757005754368000000000 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71} := by
    norm_num [Nat.primeFactors]
  have hmem := mem_of_sq_dvd (by norm_num) hpf hq hdvd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact absurd rfl hq2
  · haveI : Fact (Nat.Prime 3) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair h3
  · haveI : Fact (Nat.Prime 5) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair h5
  · haveI : Fact (Nat.Prime 7) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair h7
  · exact h11
  · haveI : Fact (Nat.Prime 13) := ⟨hq⟩
    exact WCOn.of_hasNoncommPair h13
  all_goals (exfalso; norm_num at hdvd)

theorem wcSporadicAt_M_of_eleven
    [Finite (Carrier .M)] (h11 : WCOn 11 (Carrier .M)) : WCSporadicAt .M := by
  obtain ⟨-, hcard, h13⟩ := CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds
  haveI : IsSimpleGroup (Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := Carrier .M) (MulEquiv.refl _)
  exact wcSporadicAt_M_of_data hcard
    (HasNoncommPair.map e.symm.toMonoidHom e.symm.injective hasNoncommPair_three_Gmat)
    (HasNoncommPair.map e.symm.toMonoidHom e.symm.injective hasNoncommPair_five_Gmat)
    (HasNoncommPair.map e.symm.toMonoidHom e.symm.injective hasNoncommPair_seven_Gmat) h13 h11

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
