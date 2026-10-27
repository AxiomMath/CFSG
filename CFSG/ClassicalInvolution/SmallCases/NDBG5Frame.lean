module

public import CFSG.ClassicalInvolution.SmallCases.NDBG5Weak
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinMain
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
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

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

abbrev TwinShapeWeakPred : ShapePred :=
  fun _ _ _ K z => TwinShapeWeak p f K z

theorem twinFrame_exists_on_weak (hΩ : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hGenT : TwinFrameGenT p f) :
    FrameExistsOnE p f (TwinShapeWeakPred (p := p) (f := f)) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hshape
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩ G hnab hp2 hq K z hz hBelow
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hshapeW : TwinShapeWeak p f K z := hshape
  obtain ⟨⟨D, hD⟩, T, hT, hTK, hTz⟩ := hshape
  let X : XCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩmod, hp := hp2,
      hq := hq, D := D }
  obtain ⟨C, ⟨S⟩⟩ := exists_twinShapeCtx_weak X hD hT hTz hTK
  obtain ⟨L⟩ := C.exists_lift S
  have htrans : ∀ M ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g L.K₁ = M := by
    intro M hM
    rw [← conjClass_eq_of_mem L.hK₁] at hM
    exact hM
  have fd : TwinFrameData (CoreAssembly.conjClass K) L.K₁ L.T₁ z L.u L.J L.t := L.frameData S
  have hset : TwinFrameSetting p f (CoreAssembly.conjClass K) L.K₁ L.T₁ L.J z L.u L.t :=
    { odd := hp2
      five := hq
      hyp := hΩmod
      aEmpty := aEmptyTwinWeak_proved hΩ G hnab hp2 hq K z hz hBelow hshapeW
      trans := htrans
      below := hBelow
      thm7 := thm7TypedBelow_of hP4 hBelow
      frame := fd }
  have hH51 : Hyp51 (Subgroup.closure ({z, L.u, L.t} : Set G)) :=
    hH G (CoreAssembly.conjClass K) L.K₁ L.T₁ L.J z L.u L.t hset
  have hbal : RankThreeBalance (Subgroup.closure ({z, L.u, L.t} : Set G)) := lemma52 G _ hH51
  have hUt : IsUniqueInvolution L.J L.t :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq L.hJt
  have hKcl : IsClassicalMember p f L.K₁ z := isClassicalMember_of_twin hΩmod L.hK₁ L.hK₁z
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
          exact hGenT G (CoreAssembly.conjClass K) L.K₁ L.T₁ L.J z L.u L.t hset ⟨D, hD⟩
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
    localLeviComponent_of_exact_of_quasisimple hΩIn.classical hqs C.D C.i₁ C.listed_levi
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

end CFSG.ClassicalInvolution.NDB
