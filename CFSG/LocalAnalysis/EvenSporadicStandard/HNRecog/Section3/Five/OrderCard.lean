module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FiveLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.GammaCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem card_eq_of_five (hI : TwoHSInterface) (hU : U35Facts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hGam : GammaFacts a z) (hT5 : TableVFacts a z)
    (hT7 : TableVIIFacts a z) (hFive : FiveFacts a z) :
    Nat.card G = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := by
  obtain ⟨x, hx⟩ := (hT7.partition.orbit 2).nonempty
  have hcardGxy : Nat.card ↥(Gxy a x) = 500 :=
    card_eq_of_isShapeFiveCubeByTwoTwo (hFive.five_E x hx)
  have hmul := card_orb5E_mul_card_Gxy hI h hT7 hx
  rw [hcardGxy] at hmul
  have hn : Nat.card ↥(orb5E a a) = 354816 := by omega
  have hG := card_eq_mul_of_gamma hI hU h hGam hT5 hT7
  rw [hn] at hG
  rw [hG]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
