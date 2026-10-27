module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Dict

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

theorem tableVII_orderOf_of_isConj_a (h : IsF5Type a z) {x : G} (hx : IsConj a x) :
    orderOf x = 2 := by
  obtain ⟨c, hc⟩ := hx
  rw [← SemiconjBy.orderOf_eq (c : G) hc, h.orderOf_a]

theorem tableVII_orderOf_of_isConj_z (h : IsF5Type a z) {x : G} (hx : IsConj z x) :
    orderOf x = 2 := by
  obtain ⟨c, hc⟩ := hx
  rw [← SemiconjBy.orderOf_eq (c : G) hc, h.orderOf_z]

theorem tableVII_sq_of_isConj_a (h : IsF5Type a z) {x : G} (hx : IsConj a x) : x ^ 2 = 1 := by
  rw [← tableVII_orderOf_of_isConj_a h hx]
  exact pow_orderOf_eq_one x

private theorem tableVII_basic_z_sq (h : IsF5Type a z) : z ^ 2 = 1 := by
  rw [← h.orderOf_z]
  exact pow_orderOf_eq_one z

theorem tableVII_mem_Gx_of_orb2A (h : IsF5Type a z) {x t : G} (hx : IsConj a x)
    (ht : t ∈ orb2A a x) : t ∈ Gx x :=
  mem_Gx_of_isConj_mul (tableVII_sq_of_isConj_a h (IsConj.refl a)) (tableVII_basic_z_sq h) hx
    ht.1 (Or.inl ht.2)

theorem tableVII_mem_Gx_of_orb2B (h : IsF5Type a z) {x t : G} (hx : IsConj a x)
    (ht : t ∈ orb2B a z x) : t ∈ Gx x :=
  mem_Gx_of_isConj_mul (tableVII_sq_of_isConj_a h (IsConj.refl a)) (tableVII_basic_z_sq h) hx
    ht.1 (Or.inr ht.2)

theorem tableVII_star (h : IsF5Type a z) (hPar : ParityFacts a z) (hT5 : TableVFacts a z)
    {c t : G} (hc : c ∈ oddSet a a) (ht : IsConj a t) (htc : t ∈ Gxy a c) :
    t ∈ orb2A a a ∩ orb2A a c ∨ t ∈ orb2B a z a ∩ orb2B a z c := by
  obtain ⟨hca, hcne, hodd, -⟩ := hc
  obtain ⟨hta, htc'⟩ := mem_Gxy.1 htc
  have ha2 : a ^ 2 = 1 := tableVII_sq_of_isConj_a h (IsConj.refl a)
  have hc2 : c ^ 2 = 1 := tableVII_sq_of_isConj_a h hca
  have ht2 : t ^ 2 = 1 := tableVII_sq_of_isConj_a h ht
  have haa : a * a = 1 := by rw [← pow_two, ha2]
  have hat : Commute a t := mem_Gx.1 hta
  have hne : t ≠ a := by
    intro he
    have hac : Commute a c := by
      have := mem_Gx.1 htc'
      rw [he] at this
      exact this.symm
    have hac2 : (a * c) ^ 2 = 1 := by rw [hac.mul_pow, ha2, hc2, one_mul]
    have h1 : orderOf (a * c) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hac2) with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h1
    apply hcne
    calc c = a⁻¹ := eq_inv_of_mul_eq_one_right h1
      _ = a := inv_eq_of_mul_eq_one_right haa
  have hat2 : (a * t) ^ 2 = 1 := by rw [hat.mul_pow, ha2, ht2, one_mul]
  have hat1 : a * t ≠ 1 := by
    intro h1
    apply hne
    calc t = a⁻¹ := eq_inv_of_mul_eq_one_right h1
      _ = a := inv_eq_of_mul_eq_one_right haa
  have hord : orderOf (a * t) = 2 := orderOf_eq_prime hat2 hat1
  have hbase : t ∈ tab5Base a := ⟨ht, by rw [hord]; exact even_two⟩
  have hconj : IsConj (a * t) (c * t) := by
    by_contra hnc
    have hev := hPar.even_of_not_conj c t hca (tableVII_orderOf_of_isConj_a h ht) htc hnc
    exact (Nat.not_even_iff_odd.2 hodd) hev
  obtain ⟨i, hi⟩ := hT5.partition.cover t hbase
  fin_cases i
  · have hi' : t ∈ orb2A a a := hi
    exact Or.inl ⟨hi', ht, hi'.2.trans hconj⟩
  · have hi' : t ∈ orb2B a z a := hi
    exact Or.inr ⟨hi', ht, hi'.2.trans hconj⟩
  · exfalso
    have hi' : t ∈ orb4A a z a := hi
    have hz1 : z = 1 := isConj_one_left.1 (hat2 ▸ hi'.2)
    have hz := h.orderOf_z
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by decide)
  · exfalso
    have hi' : t ∈ orb4B a a := hi
    have ha1 : a = 1 := isConj_one_left.1 (hat2 ▸ hi'.2)
    have ha := h.orderOf_a
    rw [ha1, orderOf_one] at ha
    exact absurd ha (by decide)
  · exfalso
    have hi' : IsConj a t ∧ orderOf (a * t) = 6 ∧ IsConj a ((a * t) ^ 3) := hi
    rw [hord] at hi'
    exact absurd hi'.2.1 (by decide)

end CFSG.EvenSporadicStandard.HNRecog.Section3
