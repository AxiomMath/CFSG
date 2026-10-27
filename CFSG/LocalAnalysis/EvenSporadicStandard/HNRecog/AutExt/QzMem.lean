module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.CentOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem mem_Qz_of_isConj_mul (h : F5Std a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj a (w * x)) : x ∈ Qz w := by
  have hcomm : w * x = x * w := h.mul_comm (Or.inr hw) (Or.inl hx) (Or.inl hwx)
  exact Section3.mem_Qz_of_isConj_mul h.iface h.typ h.loc.fusion1 hx hw hcomm.symm (hcomm ▸ hwx)

theorem not_mem_Qz_of_isConj_mul (h : F5Std a z) {w x : G} (hw : IsConj z w) (hx : IsConj a x)
    (hwx : IsConj z (w * x)) : x ∉ Qz w := by
  have hF : F5Std a w := h.of_isConj (IsConj.refl a) hw
  have hF' : F5Std x w := h.of_isConj hx hw
  have hcomm : w * x = x * w := h.mul_comm (Or.inr hw) (Or.inl hx) (Or.inr hwx)
  intro hxQ
  have hshape : IsShapeTwoTwoSixS5 ↥(Gxy w x) :=
    hF.loc.gzOrbit.self.shape_QA x hxQ hx
  have h1 : Nat.card ↥(Gxy w x) = 30720 := card_of_isShapeTwoTwoSixS5 hshape
  have horb : w ∈ orb2BB x w x :=
    ⟨IsConj.refl w, hw.symm.trans (hcomm ▸ hwx)⟩
  have h2 : Nat.card ↥(Gxy w x) = 3840 := by
    have hc := card_Gxy_2BB hF' horb
    rwa [Gxy_comm x w] at hc
  have h3 : (30720 : ℕ) = 3840 := h1.symm.trans h2
  norm_num at h3

end CFSG.EvenSporadicStandard.HNRecog.Section4
