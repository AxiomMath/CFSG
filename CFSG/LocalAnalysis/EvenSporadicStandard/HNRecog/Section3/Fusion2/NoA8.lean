module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem natCard_elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  change Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem natCard_of_isShapeTwoTwoTimesA8 {X : Type} [Group X]
    (h : IsShapeTwoTwoTimesA8 X) : Nat.card X = 4 * 20160 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_elem2 2, nat_card_alternatingGroup,
    Nat.card_fin]
  norm_num

theorem not_isConj_z_of_isShapeTwoTwoTimesA8 {G : Type} [Group G] {a z : G} (h : IsF5Type a z)
    {b : G} (hb : IsShapeTwoTwoTimesA8 ↥(Gxy a b)) : ¬ IsConj z b := by
  intro hconj
  have hle : Gxy a b ≤ Gx b := by
    rw [Gxy_eq_inf]
    exact inf_le_right
  have hdvd : Nat.card ↥(Gxy a b) ∣ Nat.card ↥(Gx b) := Subgroup.card_dvd_of_le hle
  have hcard_b : Nat.card ↥(Gx b) = 2 ^ 9 * 7200 :=
    (card_centralizer_eq_of_isConj hconj).symm.trans (card_centralizer_z_of_isF5Type h)
  rw [natCard_of_isShapeTwoTwoTimesA8 hb, hcard_b] at hdvd
  norm_num at hdvd

end CFSG.EvenSporadicStandard.HNRecog.Section3
