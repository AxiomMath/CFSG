module

import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.CStarGenThree
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Transfer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2
public import CFSG.LocalAnalysis.RankThreeUC.TIModule

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

structure S15CtxGen (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop where
  cstar : CStarGen G
  maxLocal : rankThreeIsMaxTwoLocal M
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  notLe : ¬ normalizer (T : Set G) ≤ M
  gn : GNSetting ↥M (T.subgroupOf M)
  pair : IsGNPair (T.subgroupOf M) T₁ T₂
  gnParabolic : GNParabolic (T.subgroupOf M) T₁ T₂
  gnThree : GNThree (T.subgroupOf M) T₁ T₂
  gnCentre : GNCentre (T.subgroupOf M) T₁ T₂
  gnAlt7 : GNAlt7 (T.subgroupOf M) T₁ T₂
  gnAltBig : GNAltBig (T.subgroupOf M) T₁ T₂
  witness : ∀ q ∈ sigmaSet G M, ∃ Q : Sylow q G, IsWitnessPrime q Q ∧ IsWitnessGen q Q M
  strong : ∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M
  noU4 : ∀ q ∈ sigmaSet G M, ¬ U4Shape q M
  three_le : ∀ q ∈ sigmaSet G M, 3 ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥M)
  rank_odd_off : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ sigmaSet G M →
    CFSG.Open.pRank r (⊤ : Subgroup ↥M) ≤ 3
  rank_char : ∀ q ∈ sigmaSet G M, ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T →
    (C.subgroupOf T).Characteristic → CFSG.Open.pRank q (normalizer (C : Set G)) ≤ 1
  rank_N₁ : ∀ q ∈ sigmaSet G M, CFSG.Open.pRank q (normalizer (T₁ : Set ↥M)) ≤ 1
  rank_N₂ : ∀ q ∈ sigmaSet G M, CFSG.Open.pRank q (normalizer (T₂ : Set ↥M)) ≤ 1
  rank_C : ∀ q ∈ sigmaSet G M, CFSG.Open.pRank q (gnC (T.subgroupOf M)) ≤ 1
  nonconstr : ¬ CFSG.ABGLocalTools.IsPConstrained 3 (↥M ⧸ gnC (T.subgroupOf M))
  p_mem : (sigmaSet G M).Nonempty
  factor : CFSG.LocalAnalysis.RankThreeUC.S15.GNFactor (T.subgroupOf M) T₁ T₂
  shape : CFSG.LocalAnalysis.RankThreeUC.S15.GNShape (T.subgroupOf M) T₁ T₂
  c118 : CFSG.Quasithin.IsC118Pair (T.subgroupOf M) T₁ T₂
  factorSub : ∀ X₁ : Subgroup ↥M, T.subgroupOf M ≤ X₁ →
    GNSetting ↥X₁ ((T.subgroupOf M).subgroupOf X₁) →
      CFSG.LocalAnalysis.RankThreeUC.S15.GN15.JOutCentralAt ((T.subgroupOf M).subgroupOf X₁) →
      CFSG.LocalAnalysis.RankThreeUC.S15.GNFactor ((T.subgroupOf M).subgroupOf X₁)
        (T₁.subgroupOf X₁) (T₂.subgroupOf X₁)
  cover : CFSG.LocalAnalysis.RankThreeUC.S15.GNCoverP (T.subgroupOf M) T₁ T₂ ∧
    CFSG.LocalAnalysis.RankThreeUC.S15.GNCoverSec (T.subgroupOf M) T₁ T₂

theorem S15CtxGen.good {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (h : S15CtxGen G M T T₁ T₂) :
    CFSG.LocalAnalysis.RankThreeUC.S15.GNGood (T.subgroupOf M) T₁ T₂ :=
  ⟨h.pair, h.gnParabolic, h.gnThree, h.gnCentre, h.gnAlt7, h.gnAltBig, h.factor, h.shape,
    h.c118, h.factorSub, h.cover⟩

theorem sigmaM_eq_sigmaSet {M : Subgroup G} :
    CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M = sigmaSet G M :=
  rfl

theorem S15CtxGen.of_ctx2 {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (h : CFSG.LocalAnalysis.RankThreeUC.S15.S15Ctx2 G M T T₁ T₂) :
    S15CtxGen G M T T₁ T₂ where
  cstar := RankThree.cStarGen_of_rankThreeUC h.standing h.uc
  maxLocal := h.maxLocal
  sylow := h.sylow
  notLe := h.notLe
  gn := h.gn
  pair := h.pair
  gnParabolic := h.gnParabolic
  gnThree := h.gnThree
  gnCentre := h.gnCentre
  gnAlt7 := h.gnAlt7
  gnAltBig := h.gnAltBig
  witness := by
    intro q hq
    obtain ⟨Q, hw⟩ := h.witness q hq
    exact ⟨Q, IsWitnessPrime.of_mem_sigmaA h.standing hq.1 Q, hw.toGen⟩
  strong := h.strong
  noU4 := h.noU4
  three_le := by
    intro q hq
    exact (h.rank_three q hq).ge
  rank_odd_off := by
    intro r hr hodd _
    exact h.rank_odd r hr hodd
  rank_char := h.rank_char
  rank_N₁ := h.rank_N₁
  rank_N₂ := h.rank_N₂
  rank_C := h.rank_C
  nonconstr := h.nonconstr
  p_mem := h.p_mem
  factor := h.factor
  shape := h.shape
  c118 := h.c118
  factorSub := h.factorSub
  cover := h.cover

theorem S15CtxGen.of_pair (hC : CStarGen G) {p : ℕ} (hpσ : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M)
    (hwit : ∀ q ∈ sigmaSet G M, ∃ Q : Sylow q G, IsWitnessPrime q Q ∧ IsWitnessGen q Q M)
    (hno : ∀ q ∈ sigmaSet G M, ¬ U4Shape q M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T))
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(CFSG.Quasithin.autOn M (uCore M T)))
    (hN : ¬ normalizer (T : Set G) ≤ M) (hgn : GNSetting ↥M (T.subgroupOf M))
    {T₁ T₂ : Subgroup ↥M} (hpair : IsGNPair (T.subgroupOf M) T₁ T₂)
    (h1 : GNParabolic (T.subgroupOf M) T₁ T₂) (h2 : GNThree (T.subgroupOf M) T₁ T₂)
    (h3 : GNCentre (T.subgroupOf M) T₁ T₂) (h4 : GNAlt7 (T.subgroupOf M) T₁ T₂)
    (h5 : GNAltBig (T.subgroupOf M) T₁ T₂)
    (hfac : CFSG.LocalAnalysis.RankThreeUC.S15.GNFactor (T.subgroupOf M) T₁ T₂)
    (hshape : CFSG.LocalAnalysis.RankThreeUC.S15.GNShape (T.subgroupOf M) T₁ T₂)
    (hc118 : CFSG.Quasithin.IsC118Pair (T.subgroupOf M) T₁ T₂)
    (hfacSub : ∀ X₁ : Subgroup ↥M, T.subgroupOf M ≤ X₁ →
      GNSetting ↥X₁ ((T.subgroupOf M).subgroupOf X₁) →
        CFSG.LocalAnalysis.RankThreeUC.S15.GN15.JOutCentralAt ((T.subgroupOf M).subgroupOf X₁) →
        CFSG.LocalAnalysis.RankThreeUC.S15.GNFactor ((T.subgroupOf M).subgroupOf X₁)
          (T₁.subgroupOf X₁) (T₂.subgroupOf X₁))
    (hcov : CFSG.LocalAnalysis.RankThreeUC.S15.GNCoverP (T.subgroupOf M) T₁ T₂ ∧
      CFSG.LocalAnalysis.RankThreeUC.S15.GNCoverSec (T.subgroupOf M) T₁ T₂) :
    S15CtxGen G M T T₁ T₂ := by
  have hns : ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T)) := fun hs =>
    hcon (CFSG.ABGLocalTools.isPConstrained_of_isSolvable hs)
  have key : ∀ q ∈ sigmaSet G M, ∃ Q : Sylow q G, IsWitnessPrime q Q ∧ IsWitnessGen q Q M ∧
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank q (normalizer (C : Set G)) ≤ 1) ∧
      rankThreeGamma 1 q (Q : Subgroup G) ≤ M := by
    intro q hq
    obtain ⟨Q, hq', hwq⟩ := hwit q hq
    obtain ⟨hH4, -, -, -, hH10⟩ :=
      transfer_residual_hyps_gen hC.toStandingGen hq' hwq hT hJe hns hN
    exact ⟨Q, hq', hwq, hH4, hH10⟩
  have hT'le : CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) ≤ T.subgroupOf M :=
    CFSG.LocalAnalysis.RankThreeUC.S15.omegaOneCenterOf_le_subgroup _
  refine ⟨hC, hw.maxLocal, hT, hN, hgn, hpair, h1, h2, h3, h4, h5, hwit, ?_, hno, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hfac, hshape, hc118, hfacSub, hcov⟩
  · intro q hq
    obtain ⟨Q, hq', hwq, -, hΓ⟩ := key q hq
    exact (hwq.gamma_one_le_iff hC.toStandingGen hq').mp hΓ
  · intro q hq
    obtain ⟨Q, hq', hwq, -, -⟩ := key q hq
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hwq.three_le_pRank hq'
  · intro r hr hodd hrσ
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hC.pRank_le_three_of_not_mem_sigmaSet hw.maxLocal hr hodd hrσ
  · intro q hq
    obtain ⟨Q, -, -, hCchar, -⟩ := key q hq
    exact hCchar
  · intro q hq
    obtain ⟨Q, hq', -, hCchar, -⟩ := key q hq
    exact CFSG.LocalAnalysis.RankThreeUC.S15.pRank_normalizer_pair_le_one hT.le
      (hpair.le_center.trans hT'le) hpair.char₁ hpair.ne_bot₁ hq'.prime hCchar
  · intro q hq
    obtain ⟨Q, hq', -, hCchar, -⟩ := key q hq
    exact CFSG.LocalAnalysis.RankThreeUC.S15.pRank_normalizer_pair_le_one hT.le
      hpair.le₂ hpair.char₂ hpair.ne_bot₂ hq'.prime hCchar
  · intro q hq
    obtain ⟨Q, hq', hwq, -, -⟩ := key q hq
    have hU := uCore_le_and_isElemAbelian hC.charTwo hw.maxLocal.1 hT
    have hk := (hwq.pRank_normalizer_of_not_isTI hC.toStandingGen hq'
      (elementary_isPGroup 2 _ hU.2) (le_normalizer_uCore M T) hT hTI).1
    rw [CFSG.LocalAnalysis.RankThreeUC.S15.gnC_subgroupOf_eq hT.le,
      ← Subgroup.inf_subgroupOf_right,
      CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf q hq'.prime _ _ inf_le_right,
      inf_comm]
    exact hk
  · exact fun h => hcon
      ((CFSG.LocalAnalysis.RankThreeUC.S15.isPConstrained_autOn_iff_quot 3
        (CFSG.LocalAnalysis.RankThreeUC.S15.gnC_subgroupOf_eq hT.le)).mpr h)
  · exact ⟨p, hpσ, by have := hw.three_le_pRank hp; omega⟩

theorem S15CtxGen.of_hyps (hC : CStarGen G) (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (hGN : CFSG.LocalAnalysis.RankThreeUC.S15.S15GNInput) {p : ℕ}
    (hpσ : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M)
    (hwit : ∀ q ∈ sigmaSet G M, ∃ Q : Sylow q G, IsWitnessPrime q Q ∧ IsWitnessGen q Q M)
    (hno : ∀ q ∈ sigmaSet G M, ¬ U4Shape q M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T))
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(CFSG.Quasithin.autOn M (uCore M T)))
    (hN : ¬ normalizer (T : Set G) ≤ M) :
    ∃ T₁ T₂ : Subgroup ↥M, S15CtxGen G M T T₁ T₂ := by
  have hTM : T ≤ M := hT.le
  have hgn := gnSetting_of_noXBlockFor hC.toStandingGen hX hw.maxLocal hT
  have hT1 : T.subgroupOf M ≠ ⊥ := by
    intro h
    apply ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hTM hx⟩ : ↥M) ∈ T.subgroupOf M := hx
    rw [h] at hx'
    simpa using hx'
  obtain ⟨T₁, T₂, hg⟩ := hGN ↥M (T.subgroupOf M) hgn hT1
  exact ⟨T₁, T₂, S15CtxGen.of_pair hC hpσ hp hw hwit hno hT hJe hTI hcon hN hgn
    hg.pair hg.parabolic hg.three hg.centre hg.alt7 hg.altBig hg.factor hg.shape hg.c118
    hg.factorSub hg.cover⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
