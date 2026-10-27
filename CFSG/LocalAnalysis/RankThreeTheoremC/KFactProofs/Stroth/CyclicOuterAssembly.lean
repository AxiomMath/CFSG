module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuterChar
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter

open CFSG.LieType.SeitzGeneration

section Assembly

private theorem stronglyEmbeddedCyclicOuter_aux (hS : SeitzOuterRankOne)
    (hChar : CharPCyclicSylow) : StronglyEmbeddedCyclicOuterKFact := by
  refine stronglyEmbeddedCyclicOuter_of_inputs hS kFactOutCyclic_holds hChar ?_ ?_
  · exact fun s p hp hp2 => CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s p hp hp2
  · intro K _ _ h p hp hp2 hd
    obtain ⟨k, hk⟩ := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K 2 1
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits h)).1.exists_card_eq
    rw [hk] at hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem stronglyEmbeddedCyclicOuter_of_seitzRankOne (hS : SeitzOuterRankOne) :
    StronglyEmbeddedCyclicOuterKFact :=
  stronglyEmbeddedCyclicOuter_aux hS charPCyclicSylow_holds

theorem stronglyEmbeddedCyclicOuter_of_seitzOuterLowN (hS : SeitzOuterLowN) :
    StronglyEmbeddedCyclicOuterKFact :=
  stronglyEmbeddedCyclicOuter_of_seitzRankOne (seitzOuterRankOne_of_lowN hS)

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter
