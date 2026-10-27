module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarRankTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSp48
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48MSide
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Data

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1CaseThreeSp48_of₂ (hSoc : StmtChevTwoSocle) (hSurv : StmtSp48Surv)
    (hDat : StmtSp48Data₂) (hM : StmtSp48MSide₂) (hTgt : StmtSp48Target)
    (hEl : KFactJStarElimSp48) (hβ : KFactBeta) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hres : D1Sp48NonsolvResidue) :
    D1CaseThreeSp48 := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp3, hd'⟩ := hd
  by_cases hsolv : Group.IsSolvable (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)))
  swap
  · exact hres G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd' e hsolv
  subst hp3
  obtain ⟨-, hsimple, hKe, hsoc⟩ :=
    hSoc G 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inl ⟨rfl, hd'⟩)) e
  set U := d1LiftX 3 H R K
  obtain ⟨hS, hZU⟩ := hSurv hd' hKe hsoc
  obtain ⟨A, hD⟩ := hDat G P M H R Rbar hcfg K hK huniq hcent d hd' e hsolv
  obtain ⟨hT, hTc⟩ := hTgt d hd' (↥K) hKe
  have hcompU := competitorsOn_socleConfigTwo hT hTc (hEl d hd' (↥K) hKe) hβ hP1L hP1A hP1S
    (P := P) (M := M) (R := R) (U := U)
  have hcompZ := competitorsOn_of_le hsimple hcompU hZU hS.ne_bot
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig K 3 P M H' R U)
    (fun H' h' => (hSurv hd' hKe h').1) (hM hD) hcompZ hsoc

theorem d1CaseThreeSp48_closed (hSchur : KFactChevTwoSurvivorSchur) (hK48 : KFactSp48Local)
    (hKD : KFactSp48Data) (hTgt : StmtSp48Target) (hEl : KFactJStarElimSp48)
    (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hOut : KFactBlockThreeOut)
    (hNine : KFactBlockThreeOrderNine) (hCGT : AschbacherLocalCGTBlock)
    (hres : D1Sp48NonsolvResidue) : D1CaseThreeSp48 :=
  d1CaseThreeSp48_of₂ (stmtChevTwoSocle_of hSchur) (stmtSp48Surv_of hK48)
    (stmtSp48Data₂_of (stmtChevTwoSocle_of hSchur) (stmtSp48Surv_of hK48) hKD)
    (stmtSp48MSide₂_of h84 h85 h86 h93 hD2 hB3 hb hOut hNine) hTgt hEl hβ hP1L hP1A hP1S h84
    hCGT hD2 hres

end CFSG.AGLEmbedding
