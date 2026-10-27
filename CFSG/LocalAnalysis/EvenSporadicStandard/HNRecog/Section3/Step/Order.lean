module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.OrderCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.OrderFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem order_of_five (hI : TwoHSInterface) (hS : SuborbitFacts) (hU : U35Facts) {G : Type}
    [Group G] [Finite G] {a z : G} (h : IsF5Type a z) (hT5 : Vert TableVFacts a z)
    (hT7 : Vert TableVIIFacts a z) (hGam : Vert GammaFacts a z) (hFive : Vert FiveFacts a z) :
    OrderFacts G := by
  have hcard : Nat.card G = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 :=
    card_eq_of_five hI hU h hGam.self hT5.self hT7.self hFive.self
  exact
    { card_eq := hcard
      exists_eleven := by
        obtain ⟨ω, -, hω⟩ := exists_orderOf_eleven hI h
        exact ⟨ω, hω⟩
      eleven_one_class := fun ω ω' hω hω' => isConj_of_orderOf_eleven hI hS h hcard hω hω'
      cent_eleven := fun ω hω =>
        isShapeCentralizerEleven_of_orderOf hI hS hU h hcard hGam.self hT7.self hFive.self hω }

end CFSG.EvenSporadicStandard.HNRecog.Section3
