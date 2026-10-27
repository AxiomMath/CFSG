module

import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Beta
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

section Holds

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem noTwoComponentsE3_holds : NoTwoComponentsE3 := by
  intro G _ _ hSet P M hs x z hx hz hmulti
  obtain ⟨L, K, hL, hLp, hK, hKp, hLK⟩ := hmulti
  obtain ⟨hPM, hxM, hzM, hpl⟩ := N3.plane63E3_of_situation hSet hs hx hz
  have hp : (5 : ℕ).Prime := Nat.prime_five
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hβs := N3.betaStructure_E3
    CFSG.LocalAnalysis.RankFourTheoremC.kFactCenterCyclicGeFive_holds GL83.I_6_10_1_proved
    GL83.I713.i_7_13_1_holds K713S.kFactSylowSplit_holds hpl ⟨L, K, hL, hK, hLK⟩
  have hI := CFSG.HardMathSupport.Solomon.Coordinator.input10_20_3_proved
  let C₀ : ComponentIndex (↥M ⧸ primeComplementCore (G := ↥M) 5) :=
    ⟨L, (CFSG.isComponent_iff_open L).2 hL⟩
  have hrk := N3.pRank_ge_of_beta_E3 hβs hI C₀ hp (by norm_num) hLp
  rw [pRank_top_subtype hp.one_lt] at hrk
  have hle : Open.pRank 5 M ≤ 3 :=
    (local_pRank_le_evenRank 5 hp (by norm_num) M hs.isCoreMaxLocal.1.1).trans hSet.rank.le
  omega

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1
