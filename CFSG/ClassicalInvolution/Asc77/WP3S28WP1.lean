module

public import CFSG.ClassicalInvolution.Asc77.WP3S28WPos
public import CFSG.ClassicalInvolution.Asc77.WP3S28BR3
public import CFSG.ClassicalInvolution.Asc77.WP3SCRP1
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.Balance.BootNoTriple
import CFSG.ClassicalInvolution.SmallCases.DSplitDefs
public import CFSG.ClassicalInvolution.Asc77.WP3S28BFuzzy
public import CFSG.ClassicalInvolution.Asc77.WP3SCUProved
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28W

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Asc77
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance.BootRank3 (omegaConnected_of_routeD)

section ChainRows

variable {p f : ℕ} [Fact p.Prime]


theorem p1_of_chain3'W (hΩall : HypOmegaModAll p f) (hAall : AEmptyChain p f)
    (hTall : NoTwinsChain p f) (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f)
    (h52 : Lemma52) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) (hshape : ChainShape3 p f (CoreAssembly.conjClass K) z)
    {M : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K) {w : G} (hw : IsClassicalMember p f M w)
    (hKM : Commutes K M) (hzw : z ≠ w) :
    LocalOddCentral (CoreAssembly.conjClass K) {z * w} := by
  have hex : ExactMembers (CoreAssembly.conjClass K) := S.exact
  have hcls : ∀ N ∈ CoreAssembly.conjClass K, ∃ u, IsClassicalMember p f N u :=
    S.inClass.classical
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) :=
    hΩall G hnab S.odd S.five K z S.cls S.below
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hshapeC : ChainShape p f (CoreAssembly.conjClass K) z := hshape.chainShape
  have hr3 : ChainShapeRank p f 3 (CoreAssembly.conjClass K) z := by
    obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hshape
    exact ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  have hpairD : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D) :=
    chainPair_model S.odd (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁ (by omega) (D.admissible i₁)
  let C : ChainCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩmod, hp := S.odd,
      hq := S.five, D := D, card_eq := hcard, i₀ := i₀, i₁ := i₁, ne := hne, tag₁ := ht₁,
      tag₀ := ht₀, rank₀ := hr₀, pair := hpairD }
  have hMC : M ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hKM z S.cls.mem x hx).symm
  have hMtq : M ∈ tqMembers (CoreAssembly.conjClass K) z :=
    centMembers_subset_tqMembers ⟨hM, hMC⟩
  obtain ⟨R₁, hR₁, hmod⟩ := C.exists_fund_i₁ hex S.p1 hMtq hw hzw
  obtain ⟨L, hLJ, hLt⟩ := C.exists_lift_of_member hMtq hw hR₁ hmod
  have htrans : ∀ N ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = N := fun N hN => hN
  have hset : ChainFrameSetting p f (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' :=
    { odd := S.odd
      five := S.five
      hyp := hΩmod
      aEmpty := hAall G hnab S.odd S.five K z S.cls S.below hshapeC
      noTwins := hTall G hnab S.odd S.five K z S.cls S.below hshapeC
      trans := htrans
      below := S.below
      shape := hshapeC
      frame := L.frameData
      symm := L.symm
      toral := L.toral }
  have hThird : ThirdZTModAt (CoreAssembly.conjClass K) K L.J z L.t :=
    fun N hN hNK hNJ hzN htN w hw => S28B.thirdZTMod_of_rank3 hset hr3 hN hNK hNJ hzN htN hw
  have hH51 : Hyp51 (Subgroup.closure ({z, L.t, L.z'} : Set G)) := hyp51_of_third h51t hset hThird
  have hframe := L.frameSideTwoStar htrans
    (hGen G (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' hset)
  have hbal : RankThreeBalance (Subgroup.closure ({z, L.t, L.z'} : Set G)) := h52 G _ hH51
  have hconn : DConnected (CoreAssembly.conjClass K) :=
    dConnected_of_omegaConnected (omegaConnected_of_routeD S.conn)
  have hcent := centralizes_of_frame hnab S.odd S.five S.inClass hconn hframe S.cls L.z_mem_B
    (L.frameData.tq_B S.odd S.five hΩmod) hbal
  have hKtw : ∀ J ∈ twinSet (CoreAssembly.conjClass K) C.K, J = C.K :=
    hTall G hnab S.odd S.five K z S.cls S.below hshapeC K (CoreAssembly.mem_conjClass_self K)
  have hcover := C.cover_two hnab hr₁ S.inClass S.ih hex S.p1 hKtw hM hw hKM hzw
  obtain ⟨s, hs1, hs2⟩ := L.exists_swap_zt htrans
  subst hLt
  have hx1 : z * L.t ≠ 1 := by
    intro h
    apply L.t_ne_z
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right hKz.sq
  have hzwc : z * L.t = L.t * z := hKM z S.cls.mem L.t hw.mem
  have hsx : s * (z * L.t) * s⁻¹ = z * L.t := by
    calc s * (z * L.t) * s⁻¹ = (s * z * s⁻¹) * (s * L.t * s⁻¹) := by group
      _ = L.t * z := by rw [hs1, hs2]
      _ = z * L.t := hzwc.symm
  have hKs : conjSub s K = M := by
    have h1 : IsUniqueInvolution (conjSub s K) L.t := by
      have := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five (S.cls.conj s)
      rwa [hs1] at this
    exact hTall G hnab S.odd S.five K z S.cls S.below hshapeC M hM (conjSub s K)
      ⟨⟨s, rfl⟩, L.t, ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hw, h1⟩
  have hcov' : ∀ N ∈ centMembers (CoreAssembly.conjClass K) (z * L.t), ∃ g : G,
      z * L.t ∈ conjSub g (Subgroup.closure ({z, L.t, L.z'} : Set G)) ∧
        InCommonComponent (z * L.t) N (conjSub g K) := by
    intro N hN
    rcases hcover N hN with h | h
    · refine ⟨1, ?_, ?_⟩
      · rw [conjSub_one]
        exact mul_mem L.z_mem_B L.t_mem_B
      · rw [conjSub_one]
        exact h
    · refine ⟨s, ?_, ?_⟩
      · rw [mem_conjSub_iff]
        have : s⁻¹ * (z * L.t) * s = z * L.t := by
          calc s⁻¹ * (z * L.t) * s = s⁻¹ * (s * (z * L.t) * s⁻¹) * s := by rw [hsx]
            _ = z * L.t := by group
        rw [this]
        exact mul_mem L.z_mem_B L.t_mem_B
      · rw [hKs]
        exact h
  exact (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal
    (CoreAssembly.mem_conjClass_self K) S.cls L.z_mem_B hcent
    (rankTwoSpan_eq_top_of_dConnected_star S.odd S.five S.inClass hframe hconn)).2 (z * L.t) hx1
    hcov'


theorem p1RowA_of_chain3'W (hΩall : HypOmegaModAll p f) (hAall : AEmptyChain p f)
    (hTall : NoTwinsChain p f) (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f)
    (h52 : Lemma52) : P1RowA p f := by
  intro G _ _ _ hnab K z S hshape M hM w hw hKM hzw
  exact p1_of_chain3'W hΩall hAall hTall hGen h51t h52 hnab S
    (chainShape3_of_localShapeA S.exact S.inClass.classical hshape) hM hw hKM hzw

theorem p1RowU_of_chain3'W (hΩall : HypOmegaModAll p f) (hAall : AEmptyChain p f)
    (hTall : NoTwinsChain p f) (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f)
    (h52 : Lemma52) : P1RowU p f := by
  intro G _ _ _ hnab K z S hshape M hM w hw hKM hzw
  exact p1_of_chain3'W hΩall hAall hTall hGen h51t h52 hnab S
    (chainShape3_of_localShapeU S.exact S.inClass.classical hshape) hM hw hKM hzw

end ChainRows

end CFSG.ClassicalInvolution.Asc77.S28W

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY

section Rows

variable {p f : ℕ} [Fact p.Prime]


structure ProductOfTwoP1ResidualsW (p f : ℕ) [Fact p.Prime] : Prop where
  genChain : ChainFrameGenT p f
  hyp51t : ChainFrameHyp51t p f
  twinSmallInner : TwinSmallInner p
  twinSmallOuter : TwinSmallOuter p
  g2d4VertexExcl : G2D4VertexExcl p f
  aEmptyTwin : AEmptyTwinExact p f
  twinInvolution : TwinInvolution p f

theorem productOfTwoP1Rows_of_fusionCoreW (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hfus : AscFusion.FusionCoreStmt p f) (h : ProductOfTwoP1ResidualsW p f) :
    ProductOfTwoP1Rows p f :=
  have hΩ : HypOmegaModAll p f := hypOmegaModAll_of_fusionCore hfus
  have hP4 : Ih8G2D4 p f := G2D4Models.ih8G2D4_unconditional
  have hH : TwinFrameHyp51 p f :=
    twinFrameHyp51_of h.twinSmallInner h.twinSmallOuter h.g2d4VertexExcl
  have hGenSL : TwinYGenTOn p f (fun t n => t = .PSL ∧ n = 4) :=
    twinYGenTOn_of_model fun tY nY _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact RouteD.TwinY.twinMFGeneration_psl4 hp2 f
  have hGenSp : TwinYGenTOn p f (fun t n => t = .PSp ∧ n = 2) :=
    twinYGenTOn_of_model fun tY nY _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact RouteD.TwinY.twinMFGeneration_psp2 hp2 (by omega)
  have hGenSU : TwinYGenTOn p f (fun t n => t = .PSU ∧ n = 4) :=
    twinYGenTOn_of_model fun tY nY _ hP => by
      obtain ⟨rfl, rfl⟩ := hP
      exact RouteD.TwinY.twinMFGeneration_psu4 hp2 hq
  ⟨S28W.p1RowA_of_chain3'W hΩ (aEmptyChain_of_hypOmega hΩ) (noTwinsChain_of_hypOmega hΩ)
      h.genChain h.hyp51t lemma52,
    S28W.p1RowU_of_chain3'W hΩ (aEmptyChain_of_hypOmega hΩ) (noTwinsChain_of_hypOmega hΩ)
      h.genChain h.hyp51t lemma52,
    p1RowSL4_of_twinExact hΩ h.aEmptyTwin hP4 hH hGenSL h.twinInvolution,
    p1RowSp2_of_twinExact hΩ h.aEmptyTwin hP4 hH hGenSp h.twinInvolution,
    p1RowSU4_of_twinExact hΩ h.aEmptyTwin hP4 hH hGenSU h.twinInvolution⟩

end Rows

end CFSG.ClassicalInvolution.Asc77
