module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Socle
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeReeF4
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3JStar
import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Closed
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem d1CaseThreeReeF4At3_of (hSoc : StmtChevTwoSocle3 G) (hDat : StmtReeF4Data)
    (hM : StmtReeF4MSide) (hTgt : StmtReeF4Target) (hEl : KFactJStarElimReeF4)
    (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) :
    D1CaseThreeLieAt3 G fun p d => p = 5 ∧ d.1 = .reeF4 2 := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp5, hd'⟩ := hd
  subst hp5
  obtain ⟨-, hsimple, hKe, hsoc⟩ :=
    hSoc 5 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inr (Or.inr ⟨rfl, hd'⟩))) e
  set U := d1LiftX 5 H R K
  obtain ⟨hD, hZU⟩ := hDat hd' hKe hsoc
  obtain ⟨hT, hTc⟩ := hTgt d hd' (↥K) hKe
  have hcompU := competitorsOn_socleConfigTwo3 hT hTc (hEl d hd' (↥K) hKe) hβ hP1L hP1A hP1S
    (P := P) (M := M) (R := R) (U := U)
  have hcompZ := competitorsOn_of_le hsimple hcompU hZU hD.surv.ne_bot
  have hind : ∀ q ∈ GLBBetaFour G, q < 5 → D1At G q := fun q hq _ =>
    absurd (four_le_evenRank_of_mem_betaFour hq) (by rw [hcfg.glob.rank]; omega)
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig K 5 P M H' R U)
    (fun H' h' => (hDat hd' hKe h').1.surv) (hM hD hind) hcompZ hsoc

theorem d1CaseThreeReeF4At3_closed (hSchur : KFactChevTwoSurvivorSchur) (hKF : KFactReeF4Local)
    (hTgt : StmtReeF4Target) (hEl : KFactJStarElimReeF4) (hP5 : KFactBlockFiveParabolic)
    (hO5 : KFactOutFiveCyclic) (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (hα : KFactThreeOrFiveDvd)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) :
    D1CaseThreeLieAt3 G fun p d => p = 5 ∧ d.1 = .reeF4 2 :=
  d1CaseThreeReeF4At3_of (stmtChevTwoSocle3_of hSchur) (stmtReeF4Data_of hKF)
    (stmtReeF4MSide_of h84 hD2 (stmtReeF4Components_of h84 h85 h86 h93 hD2 hB3 hb hα hP5 hO5))
    hTgt hEl hβ hP1L hP1A hP1S h84 hCGT hD2

end CFSG.LocalAnalysis.RankThreeTheoremC
