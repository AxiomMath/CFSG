module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarRankTwo
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def StmtReeF4Target : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), IsReeFFourFiveIndex d → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* CatGroup d) → JStarTargetTwo 5 (5 ^ 5) L ∧ JStarTargetCard 5 4 (5 ^ 5) L

@[expose] def KFactJStarElimReeF4 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), IsReeFFourFiveIndex d → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* CatGroup d) → JStarElimOf 5 (5 ^ 5) L

theorem d1CaseThreeReeF4_of (hSoc : StmtChevTwoSocle) (hDat : StmtReeF4Data)
    (hM : StmtReeF4MSide) (hTgt : StmtReeF4Target) (hEl : KFactJStarElimReeF4)
    (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) : D1CaseThreeReeF4 := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp5, hd'⟩ := hd
  subst hp5
  obtain ⟨-, hsimple, hKe, hsoc⟩ :=
    hSoc G 5 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inr (Or.inr ⟨rfl, hd'⟩))) e
  set U := d1LiftX 5 H R K
  obtain ⟨hD, hZU⟩ := hDat hd' hKe hsoc
  obtain ⟨hT, hTc⟩ := hTgt d hd' (↥K) hKe
  have hcompU := competitorsOn_socleConfigTwo hT hTc (hEl d hd' (↥K) hKe) hβ hP1L hP1A hP1S
    (P := P) (M := M) (R := R) (U := U)
  have hcompZ := competitorsOn_of_le hsimple hcompU hZU hD.surv.ne_bot
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig K 5 P M H' R U)
    (fun H' h' => (hDat hd' hKe h').1.surv) (hM hD hcfg.ind) hcompZ hsoc

end CFSG.AGLEmbedding
