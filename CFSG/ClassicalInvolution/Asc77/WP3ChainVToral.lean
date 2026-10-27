module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameChainMain
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

section Frames

variable (p f : ℕ) [Fact p.Prime]

@[expose] def ChainFrameAlphaT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      ∀ L : Subgroup (OddQuot t), CFSG.IsComponent L →
        MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) t L →
          alphaOf (inducedImage L (modOdd t (Subgroup.closure ({z, t, z'} : Set G)))) = ⊥

@[expose] def ChainFrameAlphaZT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      ∀ L : Subgroup (OddQuot (z * t)), CFSG.IsComponent L →
        MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t) L →
          alphaOf (inducedImage L (modOdd (z * t) (Subgroup.closure ({z, t, z'} : Set G)))) = ⊥

theorem chainFrameHyp51t_of_alpha (h : ChainFrameAlphaT p f) : ChainFrameHyp51t p f := by
  intro G _ _ _ Ω K J K' z t z' hs
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have htB : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hzB : z ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hKt : K ∈ ExactLayer.tqMembers Ω t :=
    ExactLayer.mem_tqMembers_iff.mpr ⟨hd.mem, hd.tq_B hp hq hΩ htB⟩
  refine ⟨FrameVertex.uniq_of_witness hp hq hΩ.conjInvariant hΩ.classical hs.below
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.ht.sq)
    (Balance.not_subset_center_of_ne_one hs.nonabelian hd.ht.ne_one)
    (hd.isElemAbelian hp hΩ) htB hd.ht.ne_one hzB hd.hz.ne_one (hd.t_ne_z hp hq hΩ).symm hKt
    (isClassicalMember_of_twin hΩ hd.mem hd.hz), ?_⟩
  intro L hL hmov
  exact h G Ω K J K' z t z' hs L hL hmov

theorem chainFrameHyp51zt_of_alpha (h : ChainFrameAlphaZT p f) : ChainFrameHyp51zt p f := by
  intro G _ _ _ Ω K J K' z t z' hs
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have htB : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hzB : z ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.mul_mem _ hzB htB
  have hzt : z * t = t * z := hd.comm_zt hp hΩ
  have hsq : (z * t) * (z * t) = 1 := by
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [← hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hd.hz.sq, hd.ht.sq, one_mul]
  have hne1 : z * t ≠ 1 := by
    intro h1
    have h2 : z = t⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right hd.ht.sq] at h2
    exact hd.t_ne_z hp hq hΩ h2.symm
  have hKzt : K ∈ ExactLayer.tqMembers Ω (z * t) :=
    ExactLayer.mem_tqMembers_iff.mpr ⟨hd.mem, hd.tq_B hp hq hΩ hztB⟩
  have hzne : z ≠ z * t := fun h1 =>
    hd.ht.ne_one (mul_left_cancel (a := z) (b := t) (c := 1) (by rw [mul_one]; exact h1.symm))
  refine ⟨FrameVertex.uniq_of_witness hp hq hΩ.conjInvariant hΩ.classical hs.below
    (ExactLayer.isPGroup_zpowers_of_sq_eq_one hsq)
    (Balance.not_subset_center_of_ne_one hs.nonabelian hne1)
    (hd.isElemAbelian hp hΩ) hztB hne1 hzB hd.hz.ne_one hzne hKzt
    (isClassicalMember_of_twin hΩ hd.mem hd.hz), ?_⟩
  intro L hL hmov
  exact h G Ω K J K' z t z' hs L hL hmov

theorem chainFrame_exists_on_of_alpha (hΩ : HypOmegaModAll p f) (hA : AEmptyAll p f)
    (hT : NoTwinsAll p f) (hGen : ChainFrameGenT p f) (hNine : ChainFrameNine p f)
    (hαt : ChainFrameAlphaT p f) (hαzt : ChainFrameAlphaZT p f) :
    FrameExistsOnE p f (ChainShapePred (p := p) (f := f)) :=
  chainFrame_exists_on hΩ hA hT hGen hNine (chainFrameHyp51t_of_alpha p f hαt)
    (chainFrameHyp51zt_of_alpha p f hαzt)

end Frames

end CFSG.ClassicalInvolution.Asc77
