module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTenBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesAt
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Layer
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
import CFSG.RankThree.PartOne.S11d.FinalLemmas
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.CStarGenThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {q : ℕ} {E H : Subgroup G}

@[expose] def TwelveTenGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (q : ℕ) (E H : Subgroup G),
    HypCGen G M q E H → ∀ (p : ℕ) (Q : Subgroup G), Q ∈ QSet M p → H4StarFam p M Q = ∅

@[expose] def TwelveTenThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M E H : Subgroup G),
    HypCGen G M 3 E H → ∀ Q : Subgroup G, Q ∈ QSet M 3 → H4StarFam 3 M Q = ∅

theorem twelveTenThree_of_gen (h : TwelveTenGen) : TwelveTenThree := by
  intro G _ _ M E H hC Q hQ
  exact h G M 3 E H hC 3 Q hQ

@[expose] def TwelveElevenGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
      ∀ q : ℕ, q.Prime → 5 ≤ q → q ∉ sigmaSet G M →
        ∀ E : Subgroup G, E ≤ M → IsElemAbelian q E → Nat.card E = q ^ 2 →
          rankThreeGamma 1 q E ≤ M →
          ∀ H : Subgroup G, IsTwoLocal H → E ≤ H → H ≤ M

theorem o1211_of_twelveElevenGen (h : TwelveElevenGen) :
    CFSG.LocalAnalysis.RankThreeUC.S15.O1211 := by
  intro G _ _ hS hUC M hM hwit _ q hq hq5 hqσ E hEM hE hEc hΓ H hH2 hEH
  have hC : CStarGen G :=
    CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.cStarGen_of_rankThreeUC hS hUC
  obtain ⟨p, hp, -⟩ := hwit
  have hσ : (sigmaSet G M).Nonempty :=
    ⟨p, by
      simpa [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hp⟩
  have hqσ' : q ∉ sigmaSet G M := by
    simpa [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hqσ
  exact h G hC M hM hσ q hq hq5 hqσ' E hEM hE hEc hΓ H hH2 hEH

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott

theorem O1211At.of_twelveElevenGen (h : Section14.TwelveElevenGen) {G : Type} [Group G]
    [Finite G] {M : Subgroup G} (hC : CStarGen G) (hM : rankThreeIsMaxTwoLocal M)
    (hσ : (sigmaSet G M).Nonempty) : O1211At G M := by
  intro q hq hq5 hqσ E hEM hE hEc hΓ H hH2 hEH
  exact h G hC M hM hσ q hq hq5
    (by simpa [sigmaSet, CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using hqσ)
    E hEM hE hEc hΓ H hH2 hEH

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {q : ℕ} {E H : Subgroup G}

theorem eq_three_of_mem_H2StarFam (h1211 : TwelveElevenGen) (hC : CStarGen G)
    (hM : rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty) {p : ℕ} {Q H : Subgroup G}
    (hQ : Q ∈ QSet M p) (hH : H ∈ H2StarFam M Q) : p = 3 := by
  haveI : IsSimpleGroup G := hC.simple
  have hp : p.Prime := QSet.prime_of_mem hQ
  have hQH : Q ≤ H := hH.1.2.1
  have hHM : ¬ H ≤ M := hH.1.2.2.1
  have hQ2 : 2 ≤ CFSG.Open.pRank p Q := QSet.two_le_pRank_of_mem hQ
  haveI : Fact p.Prime := ⟨hp⟩
  have hQne : Q ≠ ⊥ := by
    obtain ⟨E, hEQ, hE, hEc⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) hQ2
    have hEne : E ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hEc
      exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hEc
    exact fun hbot => hEne (le_bot_iff.mp (hbot ▸ hEQ))
  have hH2 : IsTwoLocal H := isTwoLocal_of_mem_H2StarFam hC.nonab hC.charTwo hQne hH
  by_cases hpσ : p ∈ sigmaSet G M
  · exact absurd (hC.embed p hpσ.1 M hM Q (QSet.le_of_mem hQ) (QSet.isPGroup_of_mem hQ) hQ2 H
      hH2 hQH) hHM
  · rcases (mem_QSet_iff.mp hQ).2.2.2.2 with ⟨hpσ', -⟩ | ⟨E, hEQ, hE, hEc, hΓ⟩
    · exact absurd hpσ' hpσ
    · by_contra hp3
      have hp2 : p ≠ 2 := QSet.ne_two_of_mem hQ
      have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      exact hHM (h1211 G hC M hM hσ p hp hp5 hpσ E (hEQ.trans (QSet.le_of_mem hQ)) hE hEc hΓ H
        hH2 (hEQ.trans hQH))

namespace HypCGen

theorem eq_three_of_twelveEleven (h1211 : TwelveElevenGen) (h : HypCGen G M q E H) : q = 3 :=
  eq_three_of_mem_H2StarFam h1211 h.cstar h.maxLocal h.sigma_nonempty h.mem_QSet h.mem

end HypCGen

@[expose] def PreambleFiveTypes (M : Subgroup G) : Prop :=
  ∀ Q ∈ QSet M 3, ∀ H ∈ H2StarFam M Q, FiveTypes M H

theorem preambleTypes_of (h1211 : TwelveElevenGen) (hC : CStarGen G)
    (hM : rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty)
    (h : PreambleFiveTypes M) : PreambleTypes M := by
  intro p Q hQ H hH
  have hp3 : p = 3 := eq_three_of_mem_H2StarFam h1211 hC hM hσ hQ hH
  subst p
  exact ⟨rfl, h Q hQ H hH⟩

theorem kSub_subgroupOf_isSubnormal (p : ℕ) (M H : Subgroup G) :
    ((kSub p M H).subgroupOf H).IsSubnormal := by
  classical
  unfold kSub
  split_ifs with h
  · refine Subgroup.Normal.isSubnormal ?_
    have hle : sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} ≤ H :=
      sSup_le fun Y hY => hY.1
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro x k hx hk
    have hsub : sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} ≤
        (sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p}).comap
          (MulAut.conj k).toMonoidHom := by
      refine sSup_le fun Y hY z hz => ?_
      have hY' : Y.map (MulAut.conj k).toMonoidHom ∈
          {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} := by
        refine ⟨?_, ?_⟩
        · rintro _ ⟨y, hy, rfl⟩
          exact H.mul_mem (H.mul_mem hk (hY.1 hy)) (H.inv_mem hk)
        · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hY.2]
      exact le_sSup hY' (Subgroup.mem_map_of_mem _ hz)
    simpa [MulAut.conj_apply] using hsub hx
  · let S : Set (Subgroup G) := {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M}
    let T : Set (Subgroup ↥H) := (fun K => K.subgroupOf H) '' S
    have hTsub : ∀ A ∈ T, A.IsSubnormal := by
      intro A hA
      obtain ⟨Y, hY, hYA⟩ := hA
      rw [← hYA]
      obtain ⟨-, K, hK, hsub, -⟩ := hY.1
      exact hsub
    have hgen : (Subgroup.closure (⋃ A ∈ T, (A : Set ↥H))).IsSubnormal :=
      (CFSG.GroupTheory.subnormal_subgroups_generated_join T hTsub).1
    have hgen_eq : sSup T = Subgroup.closure (⋃ A ∈ T, (A : Set ↥H)) := by
      rw [sSup_eq_iSup']
      simpa using Subgroup.iSup_eq_closure (fun A : ↥T => (A : Subgroup ↥H))
    have hmap : (sSup T).map H.subtype = sSup S := by
      rw [sSup_eq_iSup', Subgroup.map_iSup, sSup_eq_iSup']
      refine le_antisymm ?_ ?_
      · refine iSup_le fun A => ?_
        obtain ⟨Y, hY, hYA⟩ := A.2
        rw [← hYA, Subgroup.map_subgroupOf_eq_of_le hY.1.1]
        exact le_iSup (fun Y : ↥S => (Y : Subgroup G)) ⟨Y, hY⟩
      · refine iSup_le fun Y => ?_
        have hYT : Y.1.subgroupOf H ∈ T := ⟨Y.1, Y.2, rfl⟩
        rw [← Subgroup.map_subgroupOf_eq_of_le Y.2.1.1]
        exact le_iSup (fun A : ↥T => (A : Subgroup ↥H).map H.subtype) ⟨Y.1.subgroupOf H, hYT⟩
    have hAle : sSup S ≤ H := sSup_le fun Y hY => hY.1.1
    have hA : ((sSup S).subgroupOf H).map H.subtype = sSup S :=
      Subgroup.map_subgroupOf_eq_of_le hAle
    have hEq : (sSup S).subgroupOf H = sSup T :=
      Subgroup.map_injective H.subtype_injective (hA.trans hmap.symm)
    rw [hEq, hgen_eq]
    exact hgen

theorem condA_of_isSylowOf {M H P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P H) : CondA 3 M P H := by
  exact Or.inl (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
    hP (kSub_le 3 M H) (kSub_subgroupOf_isSubnormal 3 M H))

theorem HypCGen.exists_condA (h : HypCGen G M 3 E H) (hU : NineNineOne M 3) :
    ∃ Q : Subgroup G, E ≤ Q ∧ Q ∈ QSet M 3 ∧ H ∈ H2StarFam M Q ∧
      CFSG.ABGLocalTools.IsSylowOf 3 Q H ∧ CondA 3 M Q H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEHM : E ≤ H ⊓ M := le_inf h.E_le_H h.E_le_M
  obtain ⟨Q, hQ, hEQ⟩ := CFSG.RankThree.PartOne.exists_isSylowOf_ge hEHM h.isPGroup
  have hQH : Q ≤ H := hQ.le.trans inf_le_left
  have hQM : Q ≤ M := hQ.le.trans inf_le_right
  have hQSet : Q ∈ QSet M 3 :=
    ⟨Nat.prime_three, by norm_num, hQM, hQ.isPGroup,
      Or.inr ⟨E, hEQ, h.elem, h.card, h.gamma⟩⟩
  have hH2star : H ∈ H2StarFam M Q := mem_H2StarFam_of_le h.mem hQH
  have hσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q H :=
    (isSylowOf_of_NineNineOne h.maxLocal h.mem_QSet h.E_le_H hσ hU hQ).1
  exact ⟨Q, hEQ, hQSet, hH2star, hQsyl, condA_of_isSylowOf hQsyl⟩

theorem not_pLayerIn_le_of_component {p : ℕ} {M H : Subgroup G}
    {L : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H)} (hL : CFSG.IsComponent L)
    (hLM : ¬ L ≤ barInf p M H) : ¬ pLayerIn p H ≤ M := by
  intro hple
  apply hLM
  obtain ⟨J, hJ, hJmap⟩ := P614.P614K136.exists_isPComponent_map_eq p hL
  have hJle : J ≤ CFSG.pLayer ↥H p := le_sSup hJ
  have hJsub : J ≤ (H ⊓ M).subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr
      ⟨x.2, hple (Subgroup.mem_map_of_mem H.subtype (hJle hx))⟩
  calc L = J.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := hJmap.symm
    _ ≤ barInf p M H := Subgroup.map_mono hJsub

theorem HypCGen.pCoreOf_two_ne (h1210 : TwelveTenThree) (h : HypCGen G M 3 E H)
    (hU : NineNineOne M 3) : pCoreOf 2 H ≠ pCoreOf 2 (H ⊓ M) := by
  obtain ⟨Q, -, hQ, hHQ, -, hCondA⟩ := h.exists_condA hU
  have hH4empty : H4StarFam 3 M Q = ∅ := h1210 G M E H h Q hQ
  have hHnotH4 : H ∉ H4Fam 3 M Q := by
    intro hmem
    have hmem' : H ∈ H4StarFam 3 M Q := ⟨hHQ, hmem⟩
    rw [hH4empty] at hmem'
    exact hmem'
  exact fun heq => hHnotH4 ⟨hHQ.1, hCondA, heq⟩

theorem HypCGen.exists_component_not_le (h1210 : TwelveTenThree)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h : HypCGen G M 3 E H) (hU : NineNineOne M 3) :
    ∃ L : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent L ∧ ¬ L ≤ barInf 3 M H ∧
      (IsL34Type ↥L ∨ IsA11Type ↥L) := by
  have hσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet
  exact h97 G M E H E h.toNineSettingGen h.mem_H2Fam hσ (h.pCoreOf_two_ne h1210 hU).symm

theorem pLayerNotLeAt_of {M : Subgroup G} (h1211 : TwelveElevenGen) (h1210 : TwelveTenThree)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (hU : NineNineOneAt M) : PLayerNotLeAt M := by
  intro q E H h
  have hq3 : q = 3 := h.eq_three_of_twelveEleven h1211
  subst q
  obtain ⟨L, hL, hLnot, -⟩ := h.exists_component_not_le h1210 h97 (hU 3 E H h)
  exact not_pLayerIn_le_of_component hL hLnot

theorem agl81FourteenFifteen_of_twelve
    (hF : KFactL34FixedPointsGen) (h10 : NineTenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleFiveTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M ∧
          FourteenFifteenNormAt M ∧ NineNineOneAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_nineTen hF h10 ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hch, h1, h2, hN, hU⟩ := h G hC M hM hσ
  exact ⟨preambleTypes_of h1211 hC hM hσ hpre, hch, h1, h2, hN,
    pLayerNotLeAt_of h1211 h1210 h97 hU, hU⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
