module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinSide
public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCNine
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51Stmt
public import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
public import CFSG.ClassicalInvolution.MilestoneAssemblyCore
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import Certificates.Certificate110
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section Levi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem localLeviComponent_of_exact_of_quasisimple
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hqs : ∀ L ∈ Ω, CFSG.Open.IsQuasisimple L) {z : G}
    (D : LocalLieSystemAt p f (exactFamily Ω z) z) (i : Fin D.card)
    (hi : (D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨
      HasA2Pairs (D.tag i)) :
    LocalLeviComponent p f Ω z := by
  have h : centralizingMembers (exactFamily Ω z) {z} = centralizingMembers Ω {z} :=
    (centMembers_exactFamily Ω z).trans (exactFamily_eq_centMembers_of_quasisimple hcls hqs)
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      ∀ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), ∀ i : Fin D.card,
        ((D.tag i = .PSL ∧ 3 ≤ D.rank i) ∨ D.tag i = .PSU ∨ D.tag i = .PSp ∨
          HasA2Pairs (D.tag i)) →
        ∃ D' : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
          (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), ∃ i' : Fin D'.card,
          (D'.tag i' = .PSL ∧ 3 ≤ D'.rank i') ∨ D'.tag i' = .PSU ∨ D'.tag i' = .PSp ∨
            HasA2Pairs (D'.tag i') := by
    intro S₁ S₂ h D i hi
    subst h
    exact ⟨D, i, hi⟩
  obtain ⟨D', i', hi'⟩ := key _ _ h D i hi
  exact LocalLeviComponent.of_levi D' i' hi'

theorem TwinShapeCtx.listed_levi {z : G} (C : TwinShapeCtx p f Ω z) :
    (C.D.tag C.i₁ = .PSL ∧ 3 ≤ C.D.rank C.i₁) ∨ C.D.tag C.i₁ = .PSU ∨ C.D.tag C.i₁ = .PSp ∨
      HasA2Pairs (C.D.tag C.i₁) := by
  rcases C.listed with ⟨h, -⟩ | ⟨h, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inr (Or.inr (Or.inl h)))))

theorem TwinShapeCtxCore.listed_levi {z : G} (C : TwinShapeCtxCore p f Ω z) :
    ((C.D.tag C.i₁ = .PSL ∧ 3 ≤ C.D.rank C.i₁) ∨ C.D.tag C.i₁ = .PSU ∨ C.D.tag C.i₁ = .PSp ∨
      HasA2Pairs (C.D.tag C.i₁)) ∨ C.D.tag C.i₁ = .G2 := by
  rcases C.listed with (⟨h, -⟩ | ⟨h, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | h
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inl ⟨h, by omega⟩)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by unfold HasA2Pairs; exact Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (by
      unfold HasA2Pairs; exact Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr h

end Levi

section Inputs

variable (p f : ℕ) [Fact p.Prime]

@[expose] def AEmptyTwinExact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → TwinExactShape p f K z →
        ∀ M ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) M

@[expose] def TwinFrameGenT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), TwinFrameSetting p f Ω K K' J z u t →
      TwinLieShape p f Ω z →
        CentralizerGenerationStar Ω (Subgroup.closure ({z, u, t} : Set G)) t

end Inputs

section Frames

variable {p f : ℕ} [Fact p.Prime]

theorem twinFrame_exists_on (hΩ : HypOmegaModAll p f) (hA : AEmptyTwinExact p f)
    (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) (hGenT : TwinFrameGenT p f) :
    FrameExistsOnE p f (TwinExactShapePred (p := p) (f := f)) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hshape
  have hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K) := hΩ G hnab hp2 hq K z hz hBelow
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hshapeT : TwinExactShape p f K z := hshape
  obtain ⟨⟨D, hD⟩, T, hT, hcomm, hTz⟩ := hshape
  let X : XCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩmod, hp := hp2,
      hq := hq, D := D }
  obtain ⟨C, ⟨S⟩⟩ := exists_twinShapeCtx X hD hT hTz hcomm
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
      aEmpty := hA G hnab hp2 hq K z hz hBelow hshapeT
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

end Frames

end CFSG.ClassicalInvolution.Asc77
