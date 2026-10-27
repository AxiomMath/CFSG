module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem perp_orderOf_of_isConj_a {a z : G} (h : IsF5Type a z) {x : G} (hx : IsConj a x) :
    orderOf x = 2 := by
  obtain ⟨c, hc⟩ := hx
  rw [← SemiconjBy.orderOf_eq (c : G) hc, h.orderOf_a]

theorem perp_orderOf_of_isConj_z {a z : G} (h : IsF5Type a z) {x : G} (hx : IsConj z x) :
    orderOf x = 2 := by
  obtain ⟨c, hc⟩ := hx
  rw [← SemiconjBy.orderOf_eq (c : G) hc, h.orderOf_z]

theorem perp_orderOf_eq_four {x : G} (hx : orderOf (x ^ 2) = 2) : orderOf x = 4 := by
  have h4 : x ^ 4 = 1 := by
    have h : (x ^ 2) ^ 2 = 1 := by
      have h' := pow_orderOf_eq_one (x ^ 2)
      rw [hx] at h'
      exact h'
    show x ^ (2 * 2) = 1
    rw [pow_mul]
    exact h
  have hdvd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hmem : orderOf x ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h4'
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp h1
    rw [hx1] at hx
    simp at hx
  · have hx2 : x ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one x
    rw [hx2, orderOf_one] at hx
    norm_num at hx
  · exact h4'

theorem perp_orderOf_eq_six {x : G} (hx : orderOf (x ^ 3) = 2) (hne : orderOf x ≠ 2) :
    orderOf x = 6 := by
  have h6 : x ^ 6 = 1 := by
    have h : (x ^ 3) ^ 2 = 1 := by
      have h' := pow_orderOf_eq_one (x ^ 3)
      rw [hx] at h'
      exact h'
    show x ^ (3 * 2) = 1
    rw [pow_mul]
    exact h
  have hdvd : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hmem : orderOf x ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h2 | h3 | h6'
  · have hx1 : x = 1 := orderOf_eq_one_iff.mp h1
    rw [hx1] at hx
    simp at hx
  · exact absurd h2 hne
  · have hx3 : x ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one x
    rw [hx3, orderOf_one] at hx
    norm_num at hx
  · exact h6'

theorem perp_orderOf_row_two {a z b c : G} (h : IsF5Type a z) (hb : IsConj a b)
    (hc : c ∈ sSet a z b 2) : orderOf (a * c) = 4 ∧ (a * c) ^ 2 = b := by
  have hc' : c ∈ sBase a b ∧ (a * c) ^ 2 = b := hc
  obtain ⟨-, hsq⟩ := hc'
  have hb2 : orderOf b = 2 := perp_orderOf_of_isConj_a h hb
  exact ⟨perp_orderOf_eq_four (by rw [hsq, hb2]), hsq⟩

theorem perp_orderOf_row_three {a z b c : G} (h : IsF5Type a z) (hc : c ∈ sSet a z b 3) :
    orderOf (a * c) = 4 ∧ IsConj z ((a * c) ^ 2) := by
  have hc' : c ∈ sBase a b ∧ IsConj z ((a * c) ^ 2) := hc
  obtain ⟨-, hconj⟩ := hc'
  exact ⟨perp_orderOf_eq_four (perp_orderOf_of_isConj_z h hconj), hconj⟩

theorem perp_orderOf_row_four {a z b c : G} (hc : c ∈ sSet a z b 4) : orderOf (a * c) = 3 := by
  have hc' : c ∈ sBase a b ∧ orderOf (a * c) = 3 := hc
  exact hc'.2

theorem perp_orderOf_row_five {a z b c : G} (h : IsF5Type a z) (hb : IsConj a b)
    (hc : c ∈ sSet a z b 5) : orderOf (a * c) = 6 ∧ (a * c) ^ 3 = b := by
  have hc' : c ∈ sBase a b ∧ (a * c) ^ 3 = b := hc
  obtain ⟨hbase, hcube⟩ := hc'
  have hb2 : orderOf b = 2 := perp_orderOf_of_isConj_a h hb
  have h3 : orderOf ((a * c) ^ 3) = 2 := by rw [hcube, hb2]
  refine ⟨perp_orderOf_eq_six h3 ?_, hcube⟩
  intro hord
  have hsq : (a * c) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one (a * c)
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hac : (a * c) ^ 3 = a * c := by
    rw [show (a * c) ^ 3 = (a * c) ^ (2 + 1) from rfl, pow_succ, hsq, one_mul]
  have hbc : b = a * c := by rw [← hcube, hac]
  have hab : a * b = c := by
    rw [hbc, ← mul_assoc, ← pow_two a, ha2, one_mul]
  exact hbase.2.2.2 hab.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3
