module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup

variable {G : Type} [Group G] [Finite G]

structure S15Ctx2 (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop extends S15Ctx G M T T₁ T₂ where
  p_mem : ∃ p : ℕ, p ∈ sigmaM G M
  factor : GNFactor (T.subgroupOf M) T₁ T₂
  shape : GNShape (T.subgroupOf M) T₁ T₂
  c118 : CFSG.Quasithin.IsC118Pair (T.subgroupOf M) T₁ T₂
  factorSub : ∀ X₁ : Subgroup ↥M, T.subgroupOf M ≤ X₁ →
    GNSetting ↥X₁ ((T.subgroupOf M).subgroupOf X₁) →
      GN15.JOutCentralAt ((T.subgroupOf M).subgroupOf X₁) →
      GNFactor ((T.subgroupOf M).subgroupOf X₁) (T₁.subgroupOf X₁) (T₂.subgroupOf X₁)
  cover : GNCoverP (T.subgroupOf M) T₁ T₂ ∧ GNCoverSec (T.subgroupOf M) T₁ T₂

theorem S15Ctx2.good {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (h : S15Ctx2 G M T T₁ T₂) :
    GNGood (T.subgroupOf M) T₁ T₂ :=
  ⟨h.pair, h.gnParabolic, h.gnThree, h.gnCentre, h.gnAlt7, h.gnAltBig, h.factor, h.shape, h.c118,
    h.factorSub, h.cover⟩

theorem S15Ctx.of_pair (hS : Standing G) (hUC : rankThreeUC G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hw : IsWitness p P M) (hno : NoU4All G p M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T))
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(CFSG.Quasithin.autOn M (uCore M T)))
    (hN : ¬ normalizer (T : Set G) ≤ M) (hgn : GNSetting ↥M (T.subgroupOf M))
    {T₁ T₂ : Subgroup ↥M} (hpair : IsGNPair (T.subgroupOf M) T₁ T₂)
    (h1 : GNParabolic (T.subgroupOf M) T₁ T₂) (h2 : GNThree (T.subgroupOf M) T₁ T₂)
    (h3 : GNCentre (T.subgroupOf M) T₁ T₂) (h4 : GNAlt7 (T.subgroupOf M) T₁ T₂)
    (h5 : GNAltBig (T.subgroupOf M) T₁ T₂) : S15Ctx G M T T₁ T₂ := by
  have hTM : T ≤ M := hT.le
  have hns : ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T)) := fun hs =>
    hcon (CFSG.ABGLocalTools.isPConstrained_of_isSolvable hs)
  have hMns : ¬ Group.IsSolvable ↥M :=
    not_isSolvable_of_not_isSolvable_autOn (le_normalizer_uCore M T) hns
  have hwit : ∀ q ∈ sigmaM G M, ∃ Q : Sylow q G, IsWitness q Q M := fun q hq =>
    exists_isWitness_of_two_le_pRank hS hUC hq.1 hw.maxLocal hMns hq.2
  have key : ∀ q ∈ sigmaM G M, ∃ Q : Sylow q G, IsWitness q Q M ∧
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank q (normalizer (C : Set G)) ≤ 1) ∧
      rankThreeGamma 1 q (Q : Subgroup G) ≤ M := by
    intro q hq
    obtain ⟨Q, hwq⟩ := hwit q hq
    obtain ⟨hH4, -, -, -, hH10⟩ := transfer_residual_hyps hS hq.1 hwq hT hJe hns hN
    exact ⟨Q, hwq, hH4, hH10⟩
  have hT'le : CFSG.Quasithin.omegaOneCenterOf (T.subgroupOf M) ≤ T.subgroupOf M :=
    omegaOneCenterOf_le_subgroup _
  refine ⟨hS, hUC, hw.maxLocal, hT, hN, hgn, hpair, h1, h2, h3, h4, h5, hwit, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨Q, hwq, -, hΓ⟩ := key q hq
    exact (hwq.gamma_one_le_iff hS hq.1).mp hΓ
  · intro q hq
    exact hno q hq.1 hq.2
  · intro q hq
    obtain ⟨Q, hwq, -, -⟩ := key q hq
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (hwq.pRank_eq_three hS hq.1).2
  · intro r hr hodd
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    have := local_pRank_le_evenRank r hr hodd M hw.maxLocal.1
    rw [hS.rank] at this
    exact this
  · intro q hq
    obtain ⟨Q, -, hC, -⟩ := key q hq
    exact hC
  · intro q hq
    obtain ⟨Q, -, hC, -⟩ := key q hq
    exact pRank_normalizer_pair_le_one hTM (hpair.le_center.trans hT'le) hpair.char₁ hpair.ne_bot₁
      (sigmaA_prime q hq.1) hC
  · intro q hq
    obtain ⟨Q, -, hC, -⟩ := key q hq
    exact pRank_normalizer_pair_le_one hTM hpair.le₂ hpair.char₂ hpair.ne_bot₂
      (sigmaA_prime q hq.1) hC
  · intro q hq
    obtain ⟨Q, hwq, -, hΓ⟩ := key q hq
    have hk := (hwq.ffDatum hS hq.1 hT hJe hTI hΓ).rank_ker
    rw [gnC_subgroupOf_eq hTM, ← Subgroup.inf_subgroupOf_right,
      CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf q (sigmaA_prime q hq.1) _ _
        inf_le_right, inf_comm]
    exact hk
  · exact fun h => hcon ((isPConstrained_autOn_iff_quot 3 (gnC_subgroupOf_eq hTM)).mpr h)

theorem S15Ctx2.of_hyps (hS : Standing G) (hUC : rankThreeUC G) (hX : D1NoXBlock3 G)
    (hGN : S15GNInput) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) (hno : NoU4All G p M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T))
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(CFSG.Quasithin.autOn M (uCore M T)))
    (hN : ¬ normalizer (T : Set G) ≤ M) :
    ∃ T₁ T₂ : Subgroup ↥M, S15Ctx2 G M T T₁ T₂ := by
  have hTM : T ≤ M := hT.le
  have hgn := gnSetting_M hS hUC hX hw.maxLocal hT
  have hT1 : T.subgroupOf M ≠ ⊥ := by
    intro h
    apply ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hTM hx⟩ : ↥M) ∈ T.subgroupOf M := hx
    rw [h] at hx'
    simpa using hx'
  obtain ⟨T₁, T₂, hg⟩ := hGN ↥M (T.subgroupOf M) hgn hT1
  refine ⟨T₁, T₂, ?_⟩
  have hbase := S15Ctx.of_pair hS hUC hw hno hT hJe hTI hcon hN hgn hg.pair hg.parabolic hg.three
    hg.centre hg.alt7 hg.altBig
  have hpσ : p ∈ sigmaM G M := by
    refine ⟨hp, ?_⟩
    have := (hw.pRank_eq_three hS hp).2
    omega
  exact ⟨hbase, ⟨p, hpσ⟩, hg.factor, hg.shape, hg.c118, hg.factorSub, hg.cover⟩

theorem agl81Residual7With_noU4All_of_ctx2 (hS : Standing G) (hX : D1NoXBlock3 G)
    (hGN : S15GNInput)
    (hF : ∀ (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M), S15Ctx2 G M T T₁ T₂ → False) :
    AGL81Residual7With G (NoU4All G) := by
  intro hUC p hp P M hw hno T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
  by_contra hN
  obtain ⟨T₁, T₂, hctx⟩ := S15Ctx2.of_hyps hS hUC hX hGN hp hw hno hT H2 H3 hcon hN
  exact hF M T T₁ T₂ hctx

theorem agl81Residual7NoU4_of_ctx2 (hS : Standing G) (hX : D1NoXBlock3 G) (hGN : S15GNInput)
    (h16 : AGL81Residual7U4 G)
    (hF : ∀ (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M), S15Ctx2 G M T T₁ T₂ → False) :
    AGL81Residual7NoU4 G :=
  agl81Residual7NoU4_of_core hS h16 (agl81Residual7With_noU4All_of_ctx2 hS hX hGN hF)

end CFSG.LocalAnalysis.RankThreeUC.S15
