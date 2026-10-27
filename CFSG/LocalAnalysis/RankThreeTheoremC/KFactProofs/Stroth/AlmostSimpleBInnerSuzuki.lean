module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerReduce
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

theorem chevTwoPClosureOddFamily_suzuki :
    ChevTwoPClosureOddFamily LieFamilySuzuki := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | suzuki m =>
    obtain ⟨e⟩ := he
    obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
      CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
    have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
    refine PClosureOdd.of_mulEquiv (e.trans θ).symm ?_
    intro d hd1 hdp
    haveI : Fact p.Prime := ⟨hp⟩
    have hodd : Odd (orderOf d) := by
      rw [orderOf_eq_prime hdp hd1]
      exact hp.odd_of_ne_two hp2
    haveI : Finite (CFSG.Blueprint.suzukiGroup a K) := inferInstance
    have hC := ((CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha
      hK).2 d hd1 hodd).1
    exact OddPCoreInClosure.of_odd_core fun N _ _ =>
      hC.of_dvd_nat (Subgroup.card_subgroup_dvd_card N)
  | _ => exact absurd hF (by simp [LieFamilySuzuki])

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
