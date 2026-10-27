module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Socle
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3JStar
import CFSG.LocalAnalysis.AGLEmbedding.Sp48Data
import CFSG.LocalAnalysis.AGLEmbedding.Sp48MSide

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def StmtSp48Data₂3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig3 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsSpFourEightIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) →
    Group.IsSolvable (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    ∃ A : Subgroup G, D1Sp48Data₂ P M H R (centerOf R) (d1LiftX 3 H R K) A

theorem stmtSp48Data₂3_of (hSoc : StmtChevTwoSocle3 G) (hSurv : StmtSp48Surv)
    (hKD : KFactSp48Data) : StmtSp48Data₂3 G := by
  intro _ P M H R Rbar hcfg K hK huniq hcent d hd e hsolv
  obtain ⟨hZ, -, ⟨eK⟩, hsoc⟩ :=
    hSoc 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inl ⟨rfl, hd⟩)) e
  exact exists_sp48Data₂_of_socle hSurv hKD hcfg.ext hcfg.rbar hcfg.red hK huniq
    (hcfg.centralizer_eq_bot hK huniq hcent hZ) hd eK hsoc hsolv

@[expose] def D1Sp48NonsolvResidue3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, p = 3 → IsSpFourEightIndex d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ¬ Group.IsSolvable (((H ⊓ M).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p))) → False

theorem d1CaseThreeSp48At3_of (hSoc : StmtChevTwoSocle3 G) (hSurv : StmtSp48Surv)
    (hDat : StmtSp48Data₂3 G) (hM : StmtSp48MSide₂) (hTgt : StmtSp48Target)
    (hEl : KFactJStarElimSp48) (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hres : D1Sp48NonsolvResidue3 G) :
    D1CaseThreeLieAt3 G fun p d =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q := by
  intro p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp3, hd'⟩ := hd
  by_cases hsolv : Group.IsSolvable (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)))
  swap
  · exact hres p P M H R Rbar hcfg K hK huniq hnc hcent hKD d hp3 hd' e hsolv
  subst hp3
  obtain ⟨-, hsimple, hKe, hsoc⟩ :=
    hSoc 3 P M H R Rbar hcfg K hK huniq hcent d (Or.inr (Or.inl ⟨rfl, hd'⟩)) e
  set U := d1LiftX 3 H R K
  obtain ⟨hS, hZU⟩ := hSurv hd' hKe hsoc
  obtain ⟨A, hD⟩ := hDat P M H R Rbar hcfg K hK huniq hcent d hd' e hsolv
  obtain ⟨hT, hTc⟩ := hTgt d hd' (↥K) hKe
  have hcompU := competitorsOn_socleConfigTwo3 hT hTc (hEl d hd' (↥K) hKe) hβ hP1L hP1A hP1S
    (P := P) (M := M) (R := R) (U := U)
  have hcompZ := competitorsOn_of_le hsimple hcompU hZU hS.ne_bot
  exact false_of_survivorsOn h84 hCGT hD2 (C := fun H' => D1SocleConfig K 3 P M H' R U)
    (fun H' h' => (hSurv hd' hKe h').1) (hM hD) hcompZ hsoc

theorem d1CaseThreeSp48At3_closed (hSchur : KFactChevTwoSurvivorSchur) (hK48 : KFactSp48Local)
    (hKD : KFactSp48Data) (hTgt : StmtSp48Target) (hEl : KFactJStarElimSp48)
    (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (hOut : KFactBlockThreeOut)
    (hNine : KFactBlockThreeOrderNine) (hCGT : AschbacherLocalCGTBlock)
    (hres : D1Sp48NonsolvResidue3 G) :
    D1CaseThreeLieAt3 G fun p d =>
      p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q :=
  d1CaseThreeSp48At3_of (stmtChevTwoSocle3_of hSchur) (stmtSp48Surv_of hK48)
    (stmtSp48Data₂3_of (stmtChevTwoSocle3_of hSchur) (stmtSp48Surv_of hK48) hKD)
    (stmtSp48MSide₂_of h84 h85 h86 h93 hD2 hB3 hb hOut hNine) hTgt hEl hβ hP1L hP1A hP1S h84
    hCGT hD2 hres

end CFSG.LocalAnalysis.RankThreeTheoremC
