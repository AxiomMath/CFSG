module

public import CFSG.ClassicalInvolution.Asc77.WP3S28WPos
public import CFSG.ClassicalInvolution.Asc77.WP3S28BMain
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootChain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28W

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77
open CFSG.Assembly.LowTwoRank

section Frames

variable {p f : ℕ} [Fact p.Prime]

abbrev ChainShapeNoTriplePred : ShapePred :=
  fun _ _ _ K z => ChainShape p f (CoreAssembly.conjClass K) z ∧
    ¬ CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K)

theorem chainFrame_exists_on_of_lemma52'W (hΩ : HypOmegaModAll p f) (hA : AEmptyChain p f)
    (hT : NoTwinsChain p f) (hGen : ChainFrameGenT p f) (h51t : ChainFrameHyp51t p f)
    (h52 : Lemma52) :
    FrameExistsOnE p f (ChainShapeNoTriplePred (p := p) (f := f)) := by
  rintro G _ _ _ hnab hp2 hq K z hz hBelow hconn ⟨hshape, hnoT⟩
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩ G hnab hp2 hq K z hz hBelow
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hshapeC : ChainShape p f (CoreAssembly.conjClass K) z := hshape
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  have hpairD : ChainPair (fundamentalSubgroups (D.tag i₁) (compModel D i₁).D) :=
    chainPair_model hp2 (D.tag i₁) (D.rank i₁) (D.exp i₁) ht₁ (by omega) (D.admissible i₁)
  let C : ChainCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩmod, hp := hp2,
      hq := hq, D := D, card_eq := hcard, i₀ := i₀, i₁ := i₁, ne := hne, tag₁ := ht₁,
      tag₀ := ht₀, rank₀ := hr₀, pair := hpairD }
  obtain ⟨L⟩ := C.exists_lift
  have htrans : ∀ M ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = M := fun M hM => hM
  have hset : ChainFrameSetting p f (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' :=
    { odd := hp2
      five := hq
      hyp := hΩmod
      aEmpty := hA G hnab hp2 hq K z hz hBelow hshapeC
      noTwins := hT G hnab hp2 hq K z hz hBelow hshapeC
      trans := htrans
      below := hBelow
      shape := hshapeC
      frame := L.frameData
      symm := L.symm
      toral := L.toral }
  have hframe := L.frameSideTwoStar htrans
    (hGen G (CoreAssembly.conjClass K) K L.J L.K' z L.t L.z' hset)
  have hThird : ThirdZTModAt (CoreAssembly.conjClass K) K L.J z L.t :=
    fun N hN hNK hNJ hzN htN w hw =>
      S28B.thirdZTMod_of_dconn_noIndep hset hconn hnoT hN hNK hNJ hzN htN hw
  have hH51 : Hyp51 (Subgroup.closure ({z, L.t, L.z'} : Set G)) := hyp51_of_third h51t hset hThird
  have hbal : RankThreeBalance (Subgroup.closure ({z, L.t, L.z'} : Set G)) := h52 G _ hH51
  have hΩIn : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH : LocalLieSystems p f (CoreAssembly.conjClass K) :=
    localLieSystems_of_citBelowU hΩIn hBelow
  have hcent := centralizes_of_frame hnab hp2 hq hΩIn hconn hframe hz L.z_mem_B
    (L.frameData.tq_B hp2 hq hΩmod) hbal
  have hgen := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩIn hframe hconn
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hbal
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two _ hbal.elem (by rw [hbal.card]; norm_num)
  have hKq : CFSG.Open.IsQuasisimple K :=
    Theorem5.isQuasisimple_of_member_of_deltaCore_eq_bot hnab hp2 hq hΩIn hIH
      (CoreAssembly.mem_conjClass_self K) hz
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hbal.elem hF₀.1)
      (hcent.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)
  have hqs : ∀ N ∈ CoreAssembly.conjClass K, CFSG.Open.IsQuasisimple N :=
    Theorem5.isQuasisimple_of_mem_of_single_class (exists_single_class K)
      (CoreAssembly.mem_conjClass_self K) hKq
  have hLevi : LocalLeviComponent p f (CoreAssembly.conjClass K) z :=
    localLeviComponent_of_chainShape_of_quasisimple hΩIn.classical hqs hshapeC
  refine ⟨K, z, Subgroup.closure ({z, L.t, L.z'} : Set G), {K, L.J}, z, ?_, hH51⟩
  exact
    { mem := CoreAssembly.mem_conjClass_self K
      cls := hz
      z₀A := L.z_mem_B
      tq := L.frameData.tq_B hp2 hq hΩmod
      frame := hframe
      aA := L.z_mem_B
      a1 := hKz.ne_one
      aClassical := ⟨K, CoreAssembly.mem_conjClass_self K, hz⟩
      cover := fun M hM _ => L.cover_z htrans hM
      nine := fun _ => ⟨z, L.z_mem_B, hKz.ne_one, fun M hM => L.cover_z htrans hM, hLevi⟩ }

end Frames

end CFSG.ClassicalInvolution.Asc77.S28W

