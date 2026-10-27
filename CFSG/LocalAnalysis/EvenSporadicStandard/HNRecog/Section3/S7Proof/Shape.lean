module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Star
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.LocalClosure
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.FischerAbs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem s7_shape_Gxyz_inf (a d x : G) : Gxyz a d x = Gxy a x ⊓ Gx d := by
  ext g
  simp only [Gxyz_eq_inf, Gxy_eq_inf, Subgroup.mem_inf]
  tauto

theorem s7_shape [Finite G] {a z x : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a) :
    IsShapeSym 7 ↥(Gxy a x) := by
  refine s7_fischer_abstract (Gxy a x) (orb2A a a ∩ orb2A a x) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact (s7_D_subset H hx.1 ht).1
  · intro d hd
    exact ⟨s7_sq_of_isConj_a H hd.1.1, s7_ne_one_of_isConj_a H hd.1.1⟩
  · intro d hd k hk
    exact s7_conj_D hk hd
  · intro d hd e he
    exact s7_three H hx hd he
  · exact hx.2.2
  · intro d hd
    exact s7_closure_local H hx hd (s7_star H hx hd)
  · intro d hd
    have h := H.perp.self.shape_3A d hd.1 x (s7_mem_sSet_four H hx.1 hx.2.1 hd) d hd
    rwa [s7_shape_Gxyz_inf a d x] at h

end CFSG.EvenSporadicStandard.HNRecog.Section3
