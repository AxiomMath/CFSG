module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGz_centQ_inv (hC : CSideFacts) {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    (hA : AschbacherHyp ↥(Gx z) (CFSG.pCore 2 ↥(Gx z))) :
    ∀ x : ↥(Gx z), (barOf z x) ^ 2 = 1 → barOf z x ≠ 1 →
      Nat.card (centQtilde z (x : G)) = 2 ^ 5 :=
  fun x hx hx1 => (card_centQtilde_eq h x).trans
    (hC.centQ_inv ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) hA x hx hx1)

end CFSG.EvenSporadicStandard.HNRecog.Section3
