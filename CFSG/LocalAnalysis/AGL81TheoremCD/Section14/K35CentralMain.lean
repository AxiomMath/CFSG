module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixCentral
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralLie
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralM22
import CFSG.LocalAnalysis.AGLEmbedding.SporadicMultD1CoverThree
import CFSG.LocalAnalysis.GLTheoremB.PiGenSeven
import CFSG.LieType.SeitzGeneration.QuasiHigh5UnitaryEight

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central

open CFSG.Open Subgroup

theorem kFactThreeFiveCentral_of_lists
    (hList : CFSG.LocalAnalysis.RankThreeTheoremC.KFactAlphaListM3Wide)
    (hNC : CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.NoncyclicCentreRank) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactThreeFiveCentral := by
  intro X _ _ hKX hO _hrank K E hK hZ hK2 hE hE9 hEN hΓ
  obtain ⟨hQ, hcat, hZp, hZc, hodd, hK2'⟩ :=
    alphaList_hyps_of_isComponent hNC hKX hO hK hK2
  rcases hList ↥K hQ hcat hZ hZp hZc (hK2'.trans (by norm_num)) with
    h6 | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  · exact Or.inr h6
  · haveI : Group.IsPerfect ↥K := ⟨hQ.1⟩
    exact (hΓ ((CFSG.LocalAnalysis.GLTheoremB.le_centGenI_of_seven hEN hE hodd e).trans
      (centGenI_le_rankThreeGamma hE hE9 K))).elim
  · exact (hΓ (le_rankThreeGamma_of_forall_seitzHyperGamma hE hE9 hEN fun A hA hA9 =>
      seitzHyperGamma_eq_top_of_m22 hQ hZp e hA hA9)).elim
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨T⟩ := Sylow.nonempty (p := 3) (G := ↥K)
    have h3 := (CFSG.AGLEmbedding.SporadicMultD1.weakCore_rank_onan hQ hZ hZp hZc e T).2
    exfalso
    omega
  · rcases hd with ⟨q, hdq, h3⟩ | ⟨q, hdq, h3⟩
    · by_cases h4 : q.card = 4
      · exact Or.inl ⟨⟨d, hv⟩, ⟨q, h4, hdq⟩, ⟨e⟩⟩
      · have hdq' : d = .A 2 q := hdq
        subst hdq'
        exact (hΓ (le_rankThreeGamma_of_forall_seitzHyperGamma hE hE9 hEN fun A hA hA9 =>
          seitzHyperGamma_eq_top_of_linThree hQ.1 e h3 h4 hA hA9)).elim
    · have hdq' : d = .twistedA 2 q := hdq
      subst hdq'
      by_cases h8 : q.card = 8
      · exact (hΓ (le_rankThreeGamma_of_forall_seitzHyperGamma hE hE9 hEN fun A hA hA9 =>
          CFSG.LieType.SeitzGeneration.QuasiHigh5.seitzHyperGamma_eq_top_unitary_eight
            hQ e h8 hA hA9)).elim
      · exact (hΓ (le_rankThreeGamma_of_forall_seitzHyperGamma hE hE9 hEN fun A hA hA9 =>
          seitzHyperGamma_eq_top_of_unitaryThree hQ.1 e h3 h8 hA hA9)).elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35Central
