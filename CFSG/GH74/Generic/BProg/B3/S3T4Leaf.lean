module

public import CFSG.GH74.Generic.BProg.B3.S3T4L5
public import CFSG.GH74.Generic.BProg.B3.S3T4L4
public import CFSG.GH74.Generic.BProg.B3.S3T4L3sq
public import CFSG.GH74.Generic.BProg.B3.S3T4G2

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def InnerPairU5 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (H L : Subgroup N) (v w : N) (p f : ℕ), p.Prime → p ≠ 2 →
    1 ≤ f → LieModel ↥H .PSU 5 p f → B2.ShapeInCent H v L → B2.ShapeInCent H w L →
    B2.ShapeInCent H (v * w) L → v ∈ H → w ∈ H → False

theorem leaf514Fam_l5 (hU : InnerPairU5) : Leaf514Fam (fun X _ => B2.PuL5 X) := by
  intro N _ _ H L v w h4 hP _ _ _ hsv hsw hsvw
  have hnorm : H.Normal := hsv.normal
  have hsq : ∀ t : N, B2.ShapeInCent H t L → t * t = 1 := fun t hs => by
    have := pow_orderOf_eq_one t
    rwa [hs.inv, pow_two] at this
  have hv := S3T4.mem_of_puL5 hsv.faithful hP h4 (hsq v hsv)
  have hw := S3T4.mem_of_puL5 hsv.faithful hP h4 (hsq w hsw)
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hL⟩ | ⟨-, hM⟩⟩ := hP
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := B2.T4.T4OutCore.linear_model hL
    have hF2 : (2 : F) ≠ 0 := B2.T4.T4OutCore.two_ne_zero_of_odd_card (by
      rw [hF]; exact (hp.odd_of_ne_two hp2).pow)
    exact S3T4.false_of_inner_pair_lin hsv hsw hsvw hv hw hF2 e
  · exact hU N H L v w p f hp hp2 hf hM hsv hsw hsvw hv hw

section CertifiedLeaf


theorem leaf514S3_of (hU : InnerPairU5) : Leaf514S3 :=
  ⟨leaf514Fam_l5 hU, leaf514Fam_l4m, leaf514Fam_l3sq, leaf514Fam_g2⟩

end CertifiedLeaf

end CFSG.GH74.Generic.BProg.B3
