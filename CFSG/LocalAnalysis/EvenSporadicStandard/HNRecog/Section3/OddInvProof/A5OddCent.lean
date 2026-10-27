module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.A5OddBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5CentBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped Classical

private def a5CentCardOdd (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y => y * x = x * y).card

private theorem a5_pow_eq_one_or :
    ∀ k : alternatingGroup (Fin 5), k ^ 2 = 1 ∨ k ^ 3 = 1 ∨ k ^ 5 = 1 := by
  decide +kernel

private theorem isConj_orderOf_eq {x y : alternatingGroup (Fin 5)} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq (c : alternatingGroup (Fin 5)) hc

private theorem a5_orderOf_eq_one_or_three_or_five {k : alternatingGroup (Fin 5)}
    (hodd : Odd (orderOf k)) :
    orderOf k = 1 ∨ orderOf k = 3 ∨ orderOf k = 5 := by
  rcases a5_pow_eq_one_or k with h2 | h3 | h5
  · left
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
    · exact h
    · exfalso
      rw [h] at hodd
      exact hodd.not_two_dvd_nat dvd_rfl
  · rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one h5) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

private theorem a5CentCardOdd_three :
    ∀ x : alternatingGroup (Fin 5), x ^ 3 = 1 → x ≠ 1 → a5CentCardOdd x = 3 := by
  decide +kernel

private theorem a5CentCardOdd_five :
    ∀ x : alternatingGroup (Fin 5), x ^ 5 = 1 → x ≠ 1 → a5CentCardOdd x = 5 := by
  decide +kernel

private theorem card_centralizer_a5_three {x : alternatingGroup (Fin 5)} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : alternatingGroup (Fin 5) =>
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) =
      (Finset.univ.filter fun y : alternatingGroup (Fin 5) => y * x = x * y) := by
    apply Finset.filter_congr
    intro y _
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [hfilter]
  have h := a5CentCardOdd_three x hx3 hx1
  simpa [a5CentCardOdd] using h

private theorem card_centralizer_a5_five {x : alternatingGroup (Fin 5)} (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 5 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : alternatingGroup (Fin 5) =>
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) =
      (Finset.univ.filter fun y : alternatingGroup (Fin 5) => y * x = x * y) := by
    apply Finset.filter_congr
    intro y _
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [hfilter]
  have h := a5CentCardOdd_five x hx5 hx1
  simpa [a5CentCardOdd] using h

theorem oddInv_wr_orderOf_mul {u v : A5WrTwo} (hu : u ∉ _root_.commutator A5WrTwo)
    (hv : v ∉ _root_.commutator A5WrTwo) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1)
    (hodd : Odd (orderOf (u * v))) :
    orderOf (u * v) = 1 ∨ orderOf (u * v) = 3 ∨ orderOf (u * v) = 5 := by
  obtain ⟨k, k', hkeq, hconj⟩ := oddInv_wr_outer_mul hu hv hu2 hv2
  have horder : orderOf (u * v) = orderOf k := by
    rw [hkeq]
    exact oddInv_wr_orderOf_baseEmb hconj
  rw [horder] at hodd ⊢
  exact a5_orderOf_eq_one_or_three_or_five hodd

theorem oddInv_wr_card_three {u v : A5WrTwo} (hu : u ∉ _root_.commutator A5WrTwo)
    (hv : v ∉ _root_.commutator A5WrTwo) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1)
    (h3 : orderOf (u * v) = 3) :
    Nat.card ↥(Subgroup.centralizer ({u * v} : Set A5WrTwo)) = 18 := by
  obtain ⟨k, k', hkeq, hconj⟩ := oddInv_wr_outer_mul hu hv hu2 hv2
  have hk3 : orderOf k = 3 := by
    have h1 : orderOf (u * v) = orderOf k := by
      rw [hkeq]
      exact oddInv_wr_orderOf_baseEmb hconj
    rw [← h1, h3]
  have hk'3 : orderOf k' = 3 := (isConj_orderOf_eq hconj).symm.trans hk3
  have hk3pow : k ^ 3 = 1 := by
    have h := pow_orderOf_eq_one k
    rwa [hk3] at h
  have hk'3pow : k' ^ 3 = 1 := by
    have h := pow_orderOf_eq_one k'
    rwa [hk'3] at h
  have hk1 : k ≠ 1 := by
    intro hk
    rw [hk, orderOf_one] at hk3
    norm_num at hk3
  have hk'1 : k' ≠ 1 := by
    intro hk
    rw [hk, orderOf_one] at hk'3
    norm_num at hk'3
  rw [hkeq, card_centralizer_baseEmb_of_isConj hconj,
    card_centralizer_a5_three hk3pow hk1, card_centralizer_a5_three hk'3pow hk'1]

theorem oddInv_wr_card_five {u v : A5WrTwo} (hu : u ∉ _root_.commutator A5WrTwo)
    (hv : v ∉ _root_.commutator A5WrTwo) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1)
    (h5 : orderOf (u * v) = 5) :
    Nat.card ↥(Subgroup.centralizer ({u * v} : Set A5WrTwo)) = 50 := by
  obtain ⟨k, k', hkeq, hconj⟩ := oddInv_wr_outer_mul hu hv hu2 hv2
  have hk5 : orderOf k = 5 := by
    have h1 : orderOf (u * v) = orderOf k := by
      rw [hkeq]
      exact oddInv_wr_orderOf_baseEmb hconj
    rw [← h1, h5]
  have hk'5 : orderOf k' = 5 := (isConj_orderOf_eq hconj).symm.trans hk5
  have hk5pow : k ^ 5 = 1 := by
    have h := pow_orderOf_eq_one k
    rwa [hk5] at h
  have hk'5pow : k' ^ 5 = 1 := by
    have h := pow_orderOf_eq_one k'
    rwa [hk'5] at h
  have hk1 : k ≠ 1 := by
    intro hk
    rw [hk, orderOf_one] at hk5
    norm_num at hk5
  have hk'1 : k' ≠ 1 := by
    intro hk
    rw [hk, orderOf_one] at hk'5
    norm_num at hk'5
  rw [hkeq, card_centralizer_baseEmb_of_isConj hconj,
    card_centralizer_a5_five hk5pow hk1, card_centralizer_a5_five hk'5pow hk'1]

end CFSG.EvenSporadicStandard.HNRecog.Section3
