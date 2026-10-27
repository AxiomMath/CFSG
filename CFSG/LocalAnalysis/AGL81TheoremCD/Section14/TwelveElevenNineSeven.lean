module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Preamble
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneFi22
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.HypC
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineSym
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineConseq
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Presentation.Fi22Exact
public import CFSG.Sporadic.Presentation.Fi22ExactCover
public import CFSG.Sporadic.Presentation.Fi22ExactTop
public import Certificates.Certificate13501
public import Certificates.Certificate9205
public import Certificates.Certificate9595
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem condA_of_isSylowOf_gen {q : ℕ} (hq : q.Prime) {M H Q : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q H) : CondA q M Q H := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact Or.inl (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
    hQ (kSub_le q M H) (kSub_subgroupOf_isSubnormal q M H))

theorem nineNineOne_of_nineSevenOneAt {M : Subgroup G} (hC : CStarSettingGen G M)
    (h971 : NineSevenOneAt G M) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hqσ : q ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) : NineNineOne M q := by
  intro A hAM hA hAc hAΓ
  by_contra hAU
  obtain ⟨g, Q, hn, hH2, hne⟩ := exists_nineSettingGen_of_not_mem_uniqueSet hC hq (by omega)
    hAM hA hAc hAΓ hAU
  exact hne (h971 Q _ A q hn hH2 hqσ hq5).symm

theorem o1211At_of_nineSevenOneAt (h1210 : TwelveTenGen) {M : Subgroup G}
    (hC : CStarSettingGen G M) (h971 : NineSevenOneAt G M) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1211At G M := by
  intro q hq hq5 hqσ E hEM hE hEc hΓ H₀ hH₀ hEH₀
  by_contra hH₀M
  haveI : IsSimpleGroup G := hC.cstar.simple
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  have hH₀2 : H₀ ∈ H2Fam M E := mem_H2Fam_iff.mpr
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hC.cstar.nonab H₀ hH₀, hEH₀, hH₀M,
      hC.cstar.charTwo H₀ hH₀⟩
  obtain ⟨H, hH, -⟩ := exists_mem_H2StarFam_le hH₀2
  have hσ : (sigmaSet G M).Nonempty := by
    simpa [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hC.sigma_nonempty
  have hCG : HypCGen G M q E H :=
    ⟨hC.cstar, hC.maxLocal, hσ, hq, hq2, hEM, hE, hEc, hΓ, hH⟩
  have hU : NineNineOne M q := nineNineOne_of_nineSevenOneAt hC h971 hq hq5 hqσ
  obtain ⟨Q, hQ, hEQ⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge
    (le_inf hCG.E_le_H hEM) hCG.isPGroup
  have hQH : Q ≤ H := hQ.le.trans inf_le_left
  have hQM : Q ≤ M := hQ.le.trans inf_le_right
  have hQSet : Q ∈ QSet M q :=
    ⟨hq, hq2, hQM, hQ.isPGroup, Or.inr ⟨E, hEQ, hE, hEc, hΓ⟩⟩
  have hHQ : H ∈ H2StarFam M Q := mem_H2StarFam_of_le hH hQH
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf q Q H :=
    (isSylowOf_of_NineNineOne hC.maxLocal hCG.mem_QSet hCG.E_le_H hqσ hU hQ).1
  have hn : NineSettingGen G M q Q H E 2 :=
    ⟨hC, hQSet, mem_HFam_iff.mpr ⟨hCG.ne_top, hQH, hCG.not_le⟩,
      ⟨Or.inl rfl, hEQ, hE, hEc, by simpa using hΓ⟩⟩
  have h97 : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := h971 Q H E q hn hHQ.1 hqσ hq5
  have hempty : H4StarFam q M Q = ∅ := h1210 G M q E H hCG q Q hQSet
  have hmem : H ∈ H4StarFam q M Q :=
    ⟨hHQ, hHQ.1, condA_of_isSylowOf_gen hq hQsyl, h97.symm⟩
  rw [hempty] at hmem
  exact hmem

theorem twelveElevenGen_of_nineSevenOneGen (h1210 : TwelveTenGen) (h971 : NineSevenOneGen) :
    TwelveElevenGen := by
  intro G _ _ hC M hM hσ q hq hq5 hqσ E hEM hE hEc hΓ H hH hEH
  have hCS : CStarSettingGen G M :=
    ⟨hC, hM, by simpa [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hσ⟩
  exact o1211At_of_nineSevenOneAt h1210 hCS h971.nineSevenOneAt q hq hq5
    (by simpa [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hqσ)
    E hEM hE hEc hΓ H hH hEH

theorem o1211_of_nineSevenOne (h1210 : TwelveTenGen) (h971 : NineSevenOne) :
    CFSG.LocalAnalysis.RankThreeUC.S15.O1211 := by
  intro G _ _ hS hUC M hM hwit _ q hq hq5 hqσ E hEM hE hEc hΓ H hH hEH
  have hCS : CStarSetting G M := ⟨hS, hUC, hM, hwit⟩
  exact o1211At_of_nineSevenOneAt h1210 hCS.toGen (h971.nineSevenOneAt hCS) q hq hq5 hqσ
    E hEM hE hEc hΓ H hH hEH

theorem o1211_of_kFacts
    (h1210 : TwelveTenGen) (hB5 : KFactThreeSevenTwoGe5)
    (h5c : KFactCenterRankFive) (h2c : KFactCenterRankTwo) :
    CFSG.LocalAnalysis.RankThreeUC.S15.O1211 :=
  o1211_of_nineSevenOne h1210 (nineSevenOne_of_kFacts hB5 kFactFi22ThreeRank_holds h5c h2c)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
