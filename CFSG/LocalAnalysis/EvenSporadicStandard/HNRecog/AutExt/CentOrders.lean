module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.Card

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem card_Gx_a (h : F5Std a z) : Nat.card ↥(Gx a) = 177408000 := by
  obtain ⟨z₀, b, u, hF, -⟩ := h.loc.fusion1.self.rep_z
  rw [hF.card_eq]
  norm_num

theorem card_Gxy_2A (h : F5Std a z) {b : G} (hb : b ∈ orb2A a a) :
    Nat.card ↥(Gxy a b) = 80640 :=
  card_of_isShapeTwoTwoTimesA8 (h.loc.fusion3.self.shape_2A b hb)

theorem card_Gxy_2B (h : F5Std a z) {b : G} (hb : b ∈ orb2B a z a) :
    Nat.card ↥(Gxy a b) = 30720 :=
  card_of_isShapeTwoTwoSixS5 (h.loc.fusion3.self.shape_2B b hb)

theorem card_Gxy_2AB (h : F5Std a z) {w : G} (hw : w ∈ orb2AB a z a) :
    Nat.card ↥(Gxy a w) = 30720 :=
  card_of_isShapeTwoTwoSixS5 (h.loc.fusion3.self.shape_2AB w hw).1

theorem card_Gxy_2BB (h : F5Std a z) {w : G} (hw : w ∈ orb2BB a z a) :
    Nat.card ↥(Gxy a w) = 3840 :=
  card_of_isShapeTwoTwoTimesTwoFourA5 (h.loc.fusion3.self.shape_2BB w hw).1

end CFSG.EvenSporadicStandard.HNRecog.Section4
