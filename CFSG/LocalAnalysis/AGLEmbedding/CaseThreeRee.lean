module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.ReeLemmaJStar
import CFSG.LocalAnalysis.AGLEmbedding.ReeBorel
import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem d1CaseThreeRee_of (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hSoc : StmtReeSocle) (hBD : StmtReeBlockData)
    (hTgt : StmtReeTarget) (hElim : StmtReeElim) (hB3 : StmtBlockThree) (hLB : StmtLemmaB)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) : D1CaseThreeLieAt IsReeGTwoIndex := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hsimple, hKe, hsoc⟩ := hSoc G p P M H R Rbar hcfg K hK huniq hcent d hd e
  have hp3 : p = 3 := hd.1
  subst hp3
  set U := d1LiftX 3 H R K
  have hblock := hBD hd hKe hsoc
  have hO := hblock.pCore_ne_bot hB3 hLB h84 h85 hD2 rfl
  obtain ⟨hT, hTc⟩ := hTgt d hd (↥K) hKe hsimple
  have hE := hElim d hd (↥K) hKe hsimple
  have hcompU := competitorsOn_socleConfig hT hTc hE hβ hP1L hP1A hP1S (P := P) (M := M)
    (R := R) (U := U)
  have hcompZ := competitorsOn_of_le hsimple hcompU inf_le_left hblock.ne_bot
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig K 3 P M H' R U)
    (fun H' h' => (hBD hd hKe h').toD1SurvivorData) hO hcompZ hsoc

theorem d1CaseThreeRee_closed (hβ : KFactBeta) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (hKR1 : KFactReeSchur)
    (hKR2 : KFactReeSylowCenterTorus) (hKR3 : KFactReeCenterCentralizer)
    (hKR4 : KFactReeBorelMaximal) (hKR5 : KFactReeSylowNormalizerSolvable)
    (hKR6 : KFactReeAutElemRank) (hKR7 : KFactReeAutPCard) (hKR8 : KFactReeOrder)
    (hKR9 : KFactReeOuterSolvable) (hEL : KFactJStarElimReeLie) (hEA : KFactJStarElimReeAlt)
    (hES : KFactJStarElimReeSpor) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven) (hLB : StmtLemmaB)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) :
    D1CaseThreeLieAt IsReeGTwoIndex :=
  d1CaseThreeRee_of hβ hP1L hP1A hP1S (stmtReeSocle_of hKR1)
    (stmtReeBlockData_of (stmtReeBorel_of hKR2 hKR3 hKR4 hKR5 hKR6))
    (stmtReeTarget_of hKR2 hKR7 hKR8 hKR9) (stmtReeElim_of hEL hEA hES hKR8 hKR9)
    (stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5) hLB h84 h85 hCGT hD2

end CFSG.AGLEmbedding
