module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeLie
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBRel
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryBorel
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryData
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryBlocks
import CFSG.LocalAnalysis.AGLEmbedding.UnitaryJStar
import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.BlockThree

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem d1CaseThreeUnitary_of (hβ : KFactBeta) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (hSoc : StmtUnitarySocle)
    (hDat : StmtUnitaryData) (hJC : StmtUnitaryToJConfig) (hTgt : StmtUnitaryTarget)
    (hElim : StmtUnitaryElim) (hB3 : StmtBlockThree) (hLB : StmtLemmaBRel)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (hα : KFactThreeOrFiveDvd)
    (hβo : KFactOutElemRank) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) :
    D1CaseThreeLieAt IsUnitaryIndex := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hsimple, hKe, hsoc⟩ := hSoc G p P M H R Rbar hcfg K hK huniq hcent d hd e
  have h := hDat hd hKe hsimple hsoc hcfg.ind
  have hp2 : p ≠ 2 := hcfg.red.ne_two
  have hX := h.barM_le_pCore h84 h85 hD2 hB3 hLB hα hβo
  have hN := h.normal_sup_of_le_pCore h84 h85 hD2 hB3 hLB hX
  obtain ⟨hT, hTc⟩ := hTgt d hp2 hd h.two_le (↥K) hKe hsimple
  have hE := hElim d hp2 hd h.two_le (↥K) hKe hsimple
  have hcomp := competitorsOn_socleConfig hT hTc hE hβ hP1L hP1A hP1S (P := P) (M := M)
    (R := R) (U := d1LiftX p H R K)
  exact false_of_competitorsOn (C := fun H' => D1SocleConfig K p P M H' R (d1LiftX p H R K))
    (fun H' h' => hJC hd hKe h' hN) hcomp hsoc hCGT hD2

theorem d1CaseThreeUnitary_closed (hβ : KFactBeta) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (hKU1 : KFactUnitarySchur)
    (hKU2 : KFactUnitarySylowStructure) (hKU3 : KFactUnitarySylowCenterTorus)
    (hKU4 : KFactUnitaryTorusPPD) (hKU5 : KFactUnitaryUnipotentCentralizer)
    (hKU6 : KFactUnitaryBorelMaximal) (hKU7 : KFactUnitaryBorelPCore)
    (hKU8 : KFactUnitarySylowNormalizerSolvable) (hKU9 : KFactUnitaryAutElemRank)
    (hKU10 : KFactUnitaryAutPCard) (hKU11 : KFactUnitaryOrder)
    (hKU12 : KFactUnitaryOuterSolvable) (hEL : KFactJStarElimUnitaryLie)
    (hEA : KFactJStarElimUnitaryAlt) (hES : KFactJStarElimUnitarySpor)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hLB : StmtLemmaBRel) (hα : KFactThreeOrFiveDvd)
    (hβo : KFactOutElemRank) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) :
    D1CaseThreeLieAt IsUnitaryIndex :=
  have hB : StmtUnitaryBorel := stmtUnitaryBorel_of hKU2 hKU3 hKU4 hKU5 hKU6 hKU7 hKU8 hKU9 hKU11
  d1CaseThreeUnitary_of hβ hP1L hP1A hP1S (stmtUnitarySocle_of hKU1) (stmtUnitaryData_of hB)
    (stmtUnitaryToJConfig_of hB) (stmtUnitaryTarget_of hKU2 hKU10 hKU11 hKU12)
    (stmtUnitaryElim_of hEL hEA hES hKU2 hKU11 hKU12)
    (stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5)
    hLB h84 h85 hα hβo hCGT hD2

end CFSG.AGLEmbedding
