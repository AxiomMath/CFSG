module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

theorem card_A5WrTwo_eq : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [h5, h2]
  norm_num

theorem card_eq_of_isExtraspecialPlusByA5WrTwo {C : Type} [Group C]
    (h : IsExtraspecialPlusByA5WrTwo C) : Nat.card C = 2 ^ 9 * 7200 := by
  obtain ⟨Q, hQ, hw⟩ := h
  haveI := hQ
  have hQcard : Nat.card Q = 2 ^ 9 := by
    have hcard := hw.plus.2.1
    norm_num at hcard ⊢
    exact hcard
  have hquot : Nat.card (C ⧸ Q) = 7200 := by
    obtain ⟨e⟩ := hw.quotient
    rw [Nat.card_congr e.toEquiv, card_A5WrTwo_eq]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q, hquot, hQcard, Nat.mul_comm]

theorem card_centralizer_eq_of_isConj {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact Nat.card_congr (centralizerMulEquiv (MulAut.conj c) (by simpa using hc)).toEquiv

theorem card_centralizer_a_of_isF5Type (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) :
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11 := by
  obtain ⟨E, hE⟩ := h.cent_a
  obtain ⟨a', z', b, z₁, hF⟩ := hI.facts (centralizer ({a} : Set G)) E hE
  exact hF.card_eq

theorem card_centralizer_z_of_isF5Type {G : Type} [Group G] {a z : G} (h : IsF5Type a z) :
    Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 2 ^ 9 * 7200 :=
  card_eq_of_isExtraspecialPlusByA5WrTwo h.cent_z

theorem not_isConj_of_isF5Type (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) : ¬ IsConj a z := by
  intro hc
  have ha := card_centralizer_a_of_isF5Type hI h
  have hz := card_centralizer_z_of_isF5Type h
  have hcard := card_centralizer_eq_of_isConj hc
  rw [ha, hz] at hcard
  norm_num at hcard

end CFSG.EvenSporadicStandard.HNRecog.Section3