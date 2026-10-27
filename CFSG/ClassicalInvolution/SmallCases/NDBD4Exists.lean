module

public import CFSG.ClassicalInvolution.SmallCases.NDBD4Frame
public import CFSG.ClassicalInvolution.SmallCases.NDBD4Ctx
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinMain
import CFSG.ClassicalInvolution.SmallCases.NDBD4AEmpty
import CFSG.ClassicalInvolution.SmallCases.NDBD4GenT
import CFSG.ClassicalInvolution.SmallCases.NDBC1
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Asc77.WP3FrameP1
import CFSG.ClassicalInvolution.Asc77.WP3FrameStar
import CFSG.ClassicalInvolution.Asc77.AscT3UMain
import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinRowsOuter
import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Outer
import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
import CFSG.ClassicalInvolution.RouteD.G2D4Ih8Free
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.ClassicalInvolution.Asc77.WP3SCSGenT
import CFSG.ClassicalInvolution.AschTight.C195Wreath
import CFSG.ClassicalInvolution.AschTight.Hall196Idx
import CFSG.ClassicalInvolution.AschTight.Sec7L98J
import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.ClassicalInvolution.NDB.D4

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem exists_twinShapeCtx_d4 (X : XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A) {i₁ : Fin X.D.card}
    (hi₁ : X.D.tag i₁ = .POmegaPlus ∧ X.D.rank i₁ = 4) (h3 : 3 ≤ X.D.card) :
    ∃ C : TwinShapeCtx p f Ω z, C.toXCtx = X ∧ Nonempty C.Spec := by
  obtain ⟨i₀, i₂, h01, h12, h02, hA₀, hA₂, hlist, hK₀, hz₂, hothers⟩ :=
    exists_ctxData X hnoF hi₁ h3
  let C : TwinShapeCtx p f Ω z :=
    { toXCtx := X
      i₀ := i₀
      i₁ := i₁
      i₂ := i₂
      ne₀₁ := h01
      ne₁₂ := h12
      ne₀₂ := h02
      tag₀ := hA₀.1
      rank₀ := hA₀.2
      tag₂ := hA₂.1
      rank₂ := hA₂.2
      listed := hlist
      extra := fun j _ h1 _ => hothers j h1 }
  exact ⟨C, rfl, ⟨⟨hK₀, hz₂⟩⟩⟩

end Ctx

section Frame

variable {p f : ℕ} [Fact p.Prime]

theorem frameExists_d4 : FrameExistsOnE p f (D4FivePred p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hshape
  obtain ⟨hnoF, D, i, hi, h5⟩ := hshape
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) :=
    Cover.hypOmegaMod hnab hp2 hq hz hBelow
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  let X : XCtx p f (CoreAssembly.conjClass K) z := Cover.toXCtx hnab hp2 hq hz hBelow D
  have h3 : 3 ≤ X.D.card := by
    show 3 ≤ D.card
    omega
  have hiX : X.D.tag i = .POmegaPlus ∧ X.D.rank i = 4 := hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hothers⟩ := exists_ctxData X hnoF hiX h3
  obtain ⟨C, -, ⟨S⟩⟩ := exists_twinShapeCtx_d4 X hnoF hiX h3
  obtain ⟨L⟩ := C.exists_lift S
  have htrans : ∀ M ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g L.K₁ = M := by
    intro M hM
    rw [← Cover.conjClass_eq_of_mem L.hK₁] at hM
    exact hM
  have fd : TwinFrameData (CoreAssembly.conjClass K) L.K₁ L.T₁ z L.u L.J L.t := L.frameData S
  have hset : TwinFrameSetting p f (CoreAssembly.conjClass K) L.K₁ L.T₁ L.J z L.u L.t :=
    { odd := hp2
      five := hq
      hyp := hΩmod
      aEmpty := aEmpty_of_d4 hnab hp2 hq hz hBelow hnoF D hi
      trans := htrans
      below := hBelow
      thm7 := thm7TypedBelow_of G2D4Models.ih8G2D4_unconditional hBelow
      frame := fd }
  have hH51 : Hyp51 (Subgroup.closure ({z, L.u, L.t} : Set G)) :=
    twinFrameHyp51_of (T3CII.T3U.twinSmallInner_proved' (p := p))
      (twinSmallOuter_of_d4 (G2D4Models.Twin.twinSmallOuterD4_of_fixLift p
        (fun e => G2D4Models.Twin.d4FixLift_proved (p := p) (f := e))))
      g2d4VertexExcl_proved G _ L.K₁ L.T₁ L.J z L.u L.t hset
  have hbal : RankThreeBalance (Subgroup.closure ({z, L.u, L.t} : Set G)) := lemma52 G _ hH51
  have hUt : IsUniqueInvolution L.J L.t :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq L.hJt
  have hKcl : IsClassicalMember p f L.K₁ z := isClassicalMember_of_twin hΩmod L.hK₁ L.hK₁z
  have hzA1 : ∀ j, (X.D.tag j = .PSL ∧ X.D.rank j = 2) →
      oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (X.psi j).range := by
    intro j hA
    refine (hothers j fun h => ?_).2
    rw [h, hiX.1] at hA
    exact absurd hA.1 (by decide)
  have hgenT : CentralizerGenerationStar (CoreAssembly.conjClass K)
      (Subgroup.closure ({z, L.u, L.t} : Set G)) L.t :=
    genT_of_d4 hset X hiX.1 hiX.2 (fun j hj => (hothers j hj).1) hzA1
  have hframe : FrameSideTwoStar p f (CoreAssembly.conjClass K)
      (Subgroup.closure ({z, L.u, L.t} : Set G)) ({L.K₁, L.J} : Set (Subgroup G)) :=
    { elem := twinFrame_isElemAbelian hp2 hΩmod fd
      card := (twinFrame_natCard_eight hp2 hq hΩmod fd).ge
      subset := by
        rintro M (rfl | rfl)
        · exact L.hK₁
        · exact L.hJ.1
      nonempty := ⟨L.K₁, Set.mem_insert _ _⟩
      involution := by
        rintro M (rfl | rfl)
        · exact ⟨z, L.z_mem_B, hKcl⟩
        · exact ⟨L.t, L.t_mem_B, L.hJt⟩
      generation := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hMa).eq L.hK₁z]
          exact L.generation_z S
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hMa).eq hUt]
          exact hgenT
      link := by
        rintro a - ⟨M, (rfl | rfl), hMa⟩
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hMa).eq L.hK₁z]
          exact L.link_z_star S
        · rw [(ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hMa).eq hUt]
          exact L.link_t_star S htrans }
  have hΩIn : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH : LocalLieSystems p f (CoreAssembly.conjClass K) :=
    localLieSystems_of_citBelowU hΩIn hBelow
  have hBtq : Subgroup.closure ({z, L.u, L.t} : Set G) ≤ trivialOnQuot L.J :=
    L.B_le_trivialOnQuot hset
  have hcent := centralizes_of_frame hnab hp2 hq hΩIn hconn hframe L.hJt L.t_mem_B hBtq hbal
  have hgen := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩIn hframe hconn
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hbal
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two _ hbal.elem (by rw [hbal.card]; norm_num)
  have hJq : CFSG.Open.IsQuasisimple L.J :=
    Theorem5.isQuasisimple_of_member_of_deltaCore_eq_bot hnab hp2 hq hΩIn hIH L.hJ.1 L.hJt
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hbal.elem hF₀.1)
      (hcent.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)
  have hqs : ∀ N ∈ CoreAssembly.conjClass K, CFSG.Open.IsQuasisimple N :=
    Theorem5.isQuasisimple_of_mem_of_single_class (exists_single_class K) L.hJ.1 hJq
  have hLevi : LocalLeviComponent p f (CoreAssembly.conjClass K) z :=
    localLeviComponent_of_exact_of_quasisimple hΩIn.classical hqs D i
      (by rw [hi.1]; simp [HasA2Pairs])
  refine ⟨L.J, L.t, Subgroup.closure ({z, L.u, L.t} : Set G), {L.K₁, L.J}, z, ?_, hH51⟩
  exact
    { mem := L.hJ.1
      cls := L.hJt
      z₀A := L.t_mem_B
      tq := hBtq
      frame := hframe
      aA := L.z_mem_B
      a1 := hKz.ne_one
      aClassical := ⟨L.K₁, L.hK₁, hKcl⟩
      cover := fun M hM _ => L.cover_z S htrans hM
      nine := fun _ => ⟨z, L.z_mem_B, hKz.ne_one, fun M hM => L.cover_z S htrans hM, hLevi⟩ }

end Frame

end CFSG.ClassicalInvolution.NDB.D4
