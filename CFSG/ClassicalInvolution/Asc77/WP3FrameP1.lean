module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameChainMain
public import CFSG.ClassicalInvolution.Asc77.WP3FrameLift2
public import CFSG.ClassicalInvolution.RouteD.TriageP1Rows
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
public import CFSG.ClassicalInvolution.Asc77.WP3FrameP1Shape

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance.BootRank3 (omegaConnected_of_routeD)

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem ChainLift.frameSideTwoStar {C : ChainCtx p f Ω z} (L : ChainLift C)
    (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M)
    (hGen : CentralizerGenerationStar Ω (Subgroup.closure ({z, L.t, L.z'} : Set G)) L.t) :
    FrameSideTwoStar p f Ω (Subgroup.closure ({z, L.t, L.z'} : Set G))
      ({C.K, L.J} : Set (Subgroup G)) := by
  have hKz : IsUniqueInvolution C.K z := C.hKz
  have hKJ : ∀ a : G, IsClassicalMember p f C.K a → a = z := fun a ha =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq ha).eq hKz
  have hJt : ∀ a : G, IsClassicalMember p f L.J a → a = L.t := fun a ha =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq ha).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt)
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  exact
    { elem := L.frameData.isElemAbelian C.hp C.hΩ
      card := (L.frameData.natCard_eight C.hp C.hq C.hΩ).ge
      subset := by
        rintro M (rfl | rfl)
        · exact C.hK
        · exact L.hJ.1
      nonempty := ⟨C.K, Set.mem_insert _ _⟩
      involution := by
        rintro M (rfl | rfl)
        · exact ⟨z, L.z_mem_B, hKcl⟩
        · exact ⟨L.t, L.t_mem_B, L.hJt⟩
      generation := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [hKJ a hMa]
          exact L.generation_z
        · rw [hJt a hMa]
          exact hGen
      link := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [hKJ a hMa]
          exact L.link_z_star
        · rw [hJt a hMa]
          exact L.link_t_star htrans }

variable [IsSimpleGroup G]

theorem centralizes_of_frame (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hconn : DConnected Ω) {L₀ : Subgroup G} {z₀ : G} {A : Subgroup G}
    {S : Set (Subgroup G)} (hframe : FrameSideTwoStar p f Ω A S)
    (hcls : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A) (htq : A ≤ trivialOnQuot L₀)
    (hbal : RankThreeBalance A) :
    L₀ ≤ Subgroup.centralizer (A : Set G) := by
  have hO := componentClassificationOddCore_eq_bot_of_simple hnab
  have hgen : rankTwoSpan A = ⊤ := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩ hframe hconn
  have hc := hcls.isCentralInvolution
  have hz2 : z₀ * z₀ = 1 := hbal.mul_self hz₀A
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  by_cases hg1 : g = 1
  · rw [hg1, one_mul, mul_one]
  by_cases hgz : g = z₀
  · rw [hgz]
    exact hc.central x hx
  have hg2 : g * g = 1 := hbal.mul_self hg
  have hcomm : z₀ * g = g * z₀ := hbal.comm hz₀A hg
  have hFA : Subgroup.closure ({z₀, g} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact hz₀A
    · rw [Set.mem_singleton_iff.mp hy]
      exact hg
  have hcard : Nat.card (Subgroup.closure ({z₀, g} : Set G)) = 4 :=
    card_closure_pair_eq_four hz2 hg2 hc.ne_one hg1 (fun e => hgz e.symm) hcomm
  have hF : Subgroup.closure ({z₀, g} : Set G) ∈ signalizerFunctorEk 2 2 A :=
    ⟨hFA, by rw [hcard]; norm_num⟩
  have hα : alphaCore (Subgroup.closure ({z₀, g} : Set G)) = ⊥ :=
    TypeCSetup.alphaCore_eq_bot_of_rankTwoSpan_eq_top hO hbal hgen hF
  exact Theorem5.mem_centralizer_of_alphaCore_eq_bot hcls (htq hg) hg2 hc.ne_one hα x hx

end Frame

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def ProductSingleComponentA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeA p f 2 (CoreAssembly.conjClass K) z →
      ∀ M ∈ CoreAssembly.conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        ∀ N ∈ centMembers (CoreAssembly.conjClass K) (z * w), InCommonComponent (z * w) N K

@[expose] def ProductSingleComponentU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeU p f 2 (CoreAssembly.conjClass K) z →
      ∀ M ∈ CoreAssembly.conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        ∀ N ∈ centMembers (CoreAssembly.conjClass K) (z * w), InCommonComponent (z * w) N K

end Inputs

section P1

variable {p f : ℕ} [Fact p.Prime]

theorem p1_of_chain (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f) (hTall : NoTwinsAll p f)
    (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f) (h51zt : ChainFrameHyp51zt p f)
    (h52 : Lemma52) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hshape : ChainShape p f (CoreAssembly.conjClass K) z) {M : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass K) {w : G} (hw : IsClassicalMember p f M w)
    (hKM : Commutes K M) (hzw : z ≠ w)
    (hcov : ∀ N ∈ centMembers (CoreAssembly.conjClass K) (z * w), InCommonComponent (z * w) N K) :
    LocalOddCentral (CoreAssembly.conjClass K) {z * w} := by
  have hex : ExactMembers (CoreAssembly.conjClass K) := S.exact
  have hcls : ∀ N ∈ CoreAssembly.conjClass K, ∃ u, IsClassicalMember p f N u :=
    S.inClass.classical
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) :=
    hΩall G hnab S.odd S.five K z S.cls S.below
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hshapeC := hshape
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
      aEmpty := hAall G hnab S.odd S.five K z S.cls S.below
      noTwins := hTall G hnab S.odd S.five K z S.cls S.below
      trans := htrans
      below := S.below
      shape := hshapeC
      frame := L.frameData
      symm := L.symm
      toral := L.toral }
  have hH51 : Hyp51 (Subgroup.closure ({z, L.t, L.z'} : Set G)) :=
    chainFrameHyp51_of_vertices' p f h51t h51zt G (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z'
      hset
  have hframe := L.frameSideTwoStar htrans
    (hGen G (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' hset)
  have hbal : RankThreeBalance (Subgroup.closure ({z, L.t, L.z'} : Set G)) := h52 G _ hH51
  have hconn : DConnected (CoreAssembly.conjClass K) :=
    dConnected_of_omegaConnected (omegaConnected_of_routeD S.conn)
  have hcent := centralizes_of_frame hnab S.odd S.five S.inClass hconn hframe S.cls L.z_mem_B
    (L.frameData.tq_B S.odd S.five hΩmod) hbal
  subst hLt
  have hx1 : z * L.t ≠ 1 := by
    intro h
    apply L.t_ne_z
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right hKz.sq
  have hcov' : ∀ N ∈ centMembers (CoreAssembly.conjClass K) (z * L.t), ∃ g : G,
      z * L.t ∈ conjSub g (Subgroup.closure ({z, L.t, L.z'} : Set G)) ∧
        InCommonComponent (z * L.t) N (conjSub g K) := fun N hN => by
    refine ⟨1, ?_, ?_⟩
    · rw [conjSub_one]
      exact mul_mem L.z_mem_B L.t_mem_B
    · rw [conjSub_one]
      exact hcov N hN
  exact (stage2_of_balanced_gen hnab S.odd S.five S.inClass S.ih hbal
    (CoreAssembly.mem_conjClass_self K) S.cls L.z_mem_B hcent
    (rankTwoSpan_eq_top_of_dConnected_star S.odd S.five S.inClass hframe hconn)).2 (z * L.t) hx1
    hcov'

theorem p1RowA_of_chain (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hTall : NoTwinsAll p f) (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f)
    (h51zt : ChainFrameHyp51zt p f) (h52 : Lemma52) (hcov : ProductSingleComponentA p f) :
    P1RowA p f := by
  intro G _ _ _ hnab K z S hshape M hM w hw hKM hzw
  exact p1_of_chain hΩall hAall hTall hGen h51t h51zt h52 hnab S
    (chainShape_of_localShapeA S.exact S.inClass.classical hshape) hM hw hKM hzw
    (hcov G hnab K z S hshape M hM w hw hKM hzw)

theorem p1RowU_of_chain (hΩall : HypOmegaModAll p f) (hAall : AEmptyAll p f)
    (hTall : NoTwinsAll p f) (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f)
    (h51zt : ChainFrameHyp51zt p f) (h52 : Lemma52) (hcov : ProductSingleComponentU p f) :
    P1RowU p f := by
  intro G _ _ _ hnab K z S hshape M hM w hw hKM hzw
  exact p1_of_chain hΩall hAall hTall hGen h51t h51zt h52 hnab S
    (chainShape_of_localShapeU S.exact S.inClass.classical hshape) hM hw hKM hzw
    (hcov G hnab K z S hshape M hM w hw hKM hzw)

end P1

end CFSG.ClassicalInvolution.Asc77
