module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4P65Unify
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

theorem noTwoComponentsPlane_holds : NoTwoComponentsPlane := by
  intro p X _ _ P x z hpl hmulti
  obtain ⟨L, K, hL, hLp, hK, hKL⟩ := hmulti
  have hp := hpl.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 := hpl.five_le
  have hp2 : p ≠ 2 := by omega
  have hβs := N3.betaStructure_E3
    CFSG.LocalAnalysis.RankFourTheoremC.kFactCenterCyclicGeFive_holds GL83.I_6_10_1_proved
    GL83.I713.i_7_13_1_holds K713S.kFactSylowSplit_holds hpl ⟨L, K, hL, hK, hKL.symm⟩
  have hI := CFSG.HardMathSupport.Solomon.Coordinator.input10_20_3_proved
  let C₀ : ComponentIndex (X ⧸ primeComplementCore (G := X) p) :=
    ⟨L, (CFSG.isComponent_iff_open L).2 hL⟩
  have hrk := N3.pRank_ge_of_beta_E3 hβs hI C₀ hp hp2 hLp
  have h3 := (CFSG.SectionRank.pRank_sylow P).1
  have h4 := hpl.pRank_eq
  omega

theorem noTwoComponentsAt_of_plane (hβ : NoTwoComponentsPlane) (p : ℕ) :
    N1.NoTwoComponentsAt p := by
  intro hp5 G _ _ hS P M hsit x z hx hz hmulti
  obtain ⟨L, K, hL, hLp, hK, -, hLK⟩ := hmulti
  obtain ⟨hPM, hxM, hzM, hpl⟩ := n4_plane63E3 hS hsit hp5 hx hz
  exact hβ p ↥M (P.subtype hPM) ⟨x, hxM⟩ ⟨z, hzM⟩ hpl ⟨L, K, hL, hLp, hK, hLK.symm⟩

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
