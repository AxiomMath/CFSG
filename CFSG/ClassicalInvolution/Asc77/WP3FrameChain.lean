module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameVertex
public import CFSG.ClassicalInvolution.Asc77.WP3FrameOrbit
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

omit [Finite G] in
theorem exists_noncomm_of_isClassicalMember {L : Subgroup G} {w : G}
    (hw : IsClassicalMember p f L w) : ∃ x y : G, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have hperf := hw.perfect.commutator_eq_top
  have h1 : (⊤ : Subgroup ↥L) ≤ ⊥ := by
    rw [← hperf]
    show ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (h a b)
  have h2 : (⟨w, hw.mem⟩ : ↥L) ∈ (⊥ : Subgroup ↥L) := h1 (Subgroup.mem_top _)
  have h3 : w = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp h2)
  have h4 := hw.orderOf_eq_two
  rw [h3, orderOf_one] at h4
  omega

theorem ChainFrameSetting.nonabelian (hs : ChainFrameSetting p f Ω K J K' z t z') :
    ∃ x y : G, x * y ≠ y * x := by
  obtain ⟨z₀, hz₀⟩ := hs.hyp.classical K hs.frame.mem
  exact exists_noncomm_of_isClassicalMember hz₀

end Chain

section Vertex

variable (p f : ℕ) [Fact p.Prime]

theorem chainFrameHyp51z : ChainFrameHyp51z p f := by
  intro G _ _ _ Ω K J K' z t z' hs
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hzJ : J ∈ ExactLayer.tqMembers Ω z :=
    ExactLayer.mem_tqMembers_iff.mpr ⟨hd.memJ, hd.tq_z_J hp hq hΩ⟩
  refine FrameVertex.hyp51At_of_system_lin hp hq hΩ.conjInvariant hΩ.classical hs.below
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hz.sq)
    (Balance.not_subset_center_of_ne_one hs.nonabelian hd.hz.ne_one)
    (hd.isElemAbelian hp hΩ) (hd.natCard_eight hp hq hΩ) (Subgroup.subset_closure (by simp))
    hd.hz.ne_one (Subgroup.subset_closure (by simp)) hd.ht.ne_one (hd.t_ne_z hp hq hΩ) hzJ
    (isClassicalMember_of_twin hΩ hd.memJ hd.ht) hs.toral

theorem chainFrameHyp51_of_vertices' (ht : ChainFrameHyp51t p f) (hzt : ChainFrameHyp51zt p f) :
    ChainFrameHyp51 p f :=
  chainFrameHyp51_of_vertices (chainFrameHyp51z p f) ht hzt

end Vertex

end CFSG.ClassicalInvolution.Asc77
