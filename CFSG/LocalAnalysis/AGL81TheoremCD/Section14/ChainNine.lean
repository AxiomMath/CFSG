module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Chain
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChoiceExists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineOne
import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.TheoremCOfD
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneAt
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KNormalRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem not_mulEquiv_solvableRadical_alternatingGroup_six {K : Subgroup G}
    (hK : IsPComponentIn 3 K K) (hC3 : IsL34Star K) :
    ¬ Nonempty (↥K ⧸ CFSG.solvableRadical ↥K ≃* alternatingGroup (Fin 6)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.IsQuasisimple (threeStar K) := by
    have hKtop : CFSG.IsPComponent 3 (⊤ : Subgroup ↥K) := by
      simpa [Subgroup.subgroupOf_self] using hK.2
    have hq' :=
      CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple
        3 (⊤ : Subgroup ↥K) hKtop
    have hcore : (CFSG.pPrimeCore 3 (⊤ : Subgroup ↥K)).map
        (Subgroup.topEquiv : (⊤ : Subgroup ↥K) ≃* ↥K).toMonoidHom =
        CFSG.pPrimeCore 3 ↥K :=
      CFSG.pPrimeCore_map_iso 3 (Subgroup.topEquiv : (⊤ : Subgroup ↥K) ≃* ↥K)
    let eQ : ((⊤ : Subgroup ↥K) ⧸ CFSG.pPrimeCore 3 (⊤ : Subgroup ↥K)) ≃* threeStar K :=
      QuotientGroup.congr _ _ (Subgroup.topEquiv : (⊤ : Subgroup ↥K) ≃* ↥K) hcore
    exact CFSG.IsQuasisimple.of_mulEquiv eQ.symm hq'
  exact not_mulEquiv_solvableRadical_alternatingGroup_six_of_type hq (Or.inl hC3.1)

theorem kTwoComponentAt_of
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h14 : ∀ H ∈ H2StarAll M, CaseThree M H) (hL : PLayerNotLeAt M) :
    KTwoComponentAt M := by
  intro E H hdata
  have hC3 : CaseThree M H := h14 H hdata.mem_H2StarAll
  exact hdata.isTwoPrimeComponentIn_of_type hS (hL 3 E H hdata) hC3.1 (Or.inl hC3.2.1)

theorem nineNineOneAt_of_eq_three (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    {M : Subgroup G}
    (h3 : ∀ (q : ℕ) (E H : Subgroup G), HypCGen G M q E H → q = 3) : NineNineOneAt M := by
  intro q E H h
  have hq3 : q = 3 := h3 q E H h
  subst q
  have hσ : (CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M).Nonempty := by
    obtain ⟨p, hp⟩ := h.sigma_nonempty
    exact ⟨p, by simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hp⟩
  have hσ' : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet
  intro E₀ hE₀M hE₀ hE₀c hΓ
  exact h991 G h.cstar M h.maxLocal hσ hσ' E₀ hE₀M hE₀ (by rw [hE₀c]; norm_num) hΓ

theorem nineNineOneAt_of (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (hpre : PreambleTypes M) : NineNineOneAt M :=
  nineNineOneAt_of_eq_three h991 fun q E H h => h.eq_three hpre

theorem nineNineOneAt_of_twelveEleven (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (h1211 : TwelveElevenGen) {M : Subgroup G} : NineNineOneAt M :=
  nineNineOneAt_of_eq_three h991 fun q E H h => h.eq_three_of_twelveEleven h1211

theorem agl81FourteenFifteen_of_nine
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleFiveTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_step7 ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hpre5, hch, h1, h2⟩ := h G hC M hM hσ
  have hpre : PreambleTypes M := preambleTypes_of h1211 hC hM hσ hpre5
  have h14 : ∀ H ∈ H2StarAll M, CaseThree M H := caseThree_of_cases hpre hch h1 h2
  have hU : NineNineOneAt M := nineNineOneAt_of h991 hpre
  have hL : PLayerNotLeAt M := pLayerNotLeAt_of h1211 h1210 h97 hU
  have hTwo : KTwoComponentAt M := kTwoComponentAt_of hS h14 hL
  have hK : KNormalAt M := kNormalAt_of_preamble hpre hU hL
  exact ⟨hpre, hch, h1, h2, hTwo, hK, hL, hU⟩

theorem agl81TheoremCFour_of_nine
    (hD : CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour)
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleFiveTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremCFour :=
  CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.agl81TheoremCFour_of_theoremDFour hD
    (agl81FourteenFifteen_of_nine h1210 h1211 h97 hS h991 h)

theorem agl81FourteenFifteen_of_nineSix
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_nine h1210 h1211 h97 hS h991 ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hch, h1, h2⟩ := h G hC M hM hσ
  exact ⟨preambleFiveTypes_of h1210 h97 h96 hC hM hσ
    (nineNineOneAt_of_twelveEleven h991 h1211), hch, h1, h2⟩

theorem agl81TheoremCFour_of_nineSix
    (hD : CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour)
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremCFour :=
  CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.agl81TheoremCFour_of_theoremDFour hD
    (agl81FourteenFifteen_of_nineSix h1210 h1211 h97 h96 hS h991 h)

theorem agl81FourteenFifteen_of_choice
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (hinv : KFactL34NotInvolvedA11)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        CaseOneFalse M ∧ CaseTwoFalse M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_nineSix h1210 h1211 h97 h96 hS h991 ?_
  intro G _ _ hC M hM hσ
  obtain ⟨h1, h2⟩ := h G hC M hM hσ
  have hU : NineNineOneAt M := nineNineOneAt_of_twelveEleven h991 h1211
  have hpre : PreambleTypes M :=
    preambleTypes_of h1211 hC hM hσ (preambleFiveTypes_of h1210 h97 h96 hC hM hσ hU)
  have hL : PLayerNotLeAt M := pLayerNotLeAt_of h1211 h1210 h97 hU
  exact ⟨choiceExists_of hC hM hσ h1211 hpre hU hL hS hinv, h1, h2⟩

theorem agl81TheoremCFour_of_choice
    (hD : CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour)
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen)
    (hinv : KFactL34NotInvolvedA11)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        CaseOneFalse M ∧ CaseTwoFalse M) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremCFour :=
  CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.agl81TheoremCFour_of_theoremDFour hD
    (agl81FourteenFifteen_of_choice h1210 h1211 h97 h96 hS h991 hinv h)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
