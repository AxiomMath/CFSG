module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4L63
import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Beta
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

section Holds

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem noTwoComponentsGen_holds : NoTwoComponentsGen := by
  intro G _ _ hSet p hp5 P M hs x z hx hz hmulti
  obtain ⟨L, K, hL, hLp, hK, hLK⟩ := hmulti
  obtain ⟨hPM, hxM, hzM, hpl⟩ := n4_plane63E3 hSet hs hp5 hx hz
  have hp : p.Prime := sigmaA_prime p hs.mem_sigmaA
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := sigmaA_odd p hs.mem_sigmaA
  have hβs := N3.betaStructure_E3
    CFSG.LocalAnalysis.RankFourTheoremC.kFactCenterCyclicGeFive_holds GL83.I_6_10_1_proved
    GL83.I713.i_7_13_1_holds K713S.kFactSylowSplit_holds hpl ⟨L, K, hL, hK, hLK.symm⟩
  have hI := CFSG.HardMathSupport.Solomon.Coordinator.input10_20_3_proved
  let C₀ : ComponentIndex (↥M ⧸ primeComplementCore (G := ↥M) p) :=
    ⟨L, (CFSG.isComponent_iff_open L).2 hL⟩
  have hrk := N3.pRank_ge_of_beta_E3 hβs hI C₀ hp hp2 hLp
  rw [pRank_top_subtype hp.one_lt] at hrk
  have hle : Open.pRank p M ≤ 3 :=
    (local_pRank_le_evenRank p hp hp2 M hs.isCoreMaxLocal.1.1).trans hSet.rank.le
  omega

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
