module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem orderOf_eq_of_isConj {G : Type} [Group G] {u v : G} (h : IsConj u v) :
    orderOf u = orderOf v := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq (c : G) hc

theorem isShapeCentralizerFiveB_of_orb5E {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hPar : ParityFacts a z) (hCls : GzClassFacts a z) (hT4 : TableIVFacts a z)
    (hT6 : TableVIFacts a z) {x : G} (hx : x ∈ orb5E a a) {s : G} (hs : IsConj a s)
    (hsx : s ∈ Gxy a x) : IsShapeCentralizerFiveB ↥(Gxy s (a * x)) := by
  have ha2 : a * a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hs_order : orderOf s = 2 := (orderOf_eq_of_isConj hs).symm.trans h.orderOf_a
  have hx_order : orderOf x = 2 := (orderOf_eq_of_isConj hx.1.1).symm.trans h.orderOf_a
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs_order, pow_orderOf_eq_one]
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx_order, pow_orderOf_eq_one]
  have hax5 : orderOf (a * x) = 5 := hx.2.1
  have hsx1 : s ∈ Gx a := (mem_Gxy.mp hsx).1
  have hsx2 : s ∈ Gx x := (mem_Gxy.mp hsx).2
  have has_comm : a * s = s * a := mem_Gx.mp hsx1
  have hxs_comm : x * s = s * x := mem_Gx.mp hsx2
  have hax_nc : ¬ a * x = x * a := by
    intro hcomm
    have hcm : Commute a x := hcomm
    have h2 : (a * x) ^ 2 = 1 := by
      rw [hcm.mul_pow 2]
      simp only [pow_two, ha2, hx2, mul_one]
    have hdvd : orderOf (a * x) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hax5] at hdvd
    norm_num at hdvd
  have ha_notin : a ∉ Gx x := fun haGx => hax_nc (mem_Gx.mp haGx).symm
  have hs_ne_a : s ≠ a := fun hsa => ha_notin (by simpa [hsa] using hsx2)
  have has_sq : (a * s) ^ 2 = 1 := by
    have hcm : Commute a s := has_comm
    rw [hcm.mul_pow 2]
    simp only [pow_two, ha2, hs2, mul_one]
  have has_ne_one : a * s ≠ 1 := by
    intro h1
    have hs_eq : s = a := by
      calc s = a⁻¹ * (a * s) := by rw [inv_mul_cancel_left]
           _ = a⁻¹ * 1 := by rw [h1]
           _ = a := by rw [mul_one, inv_eq_of_mul_eq_one_right ha2]
    exact hs_ne_a hs_eq
  have has_order : orderOf (a * s) = 2 := orderOf_eq_prime (p := 2) has_sq has_ne_one
  have hconj_as_xs : IsConj (a * s) (x * s) := by
    by_contra hc
    have heven : Even (orderOf (a * x)) := hPar.even_of_not_conj x s hx.1.1 hs_order hsx hc
    rw [hax5] at heven
    norm_num at heven
  have h2ord : orderOf ((a * x) ^ 2) = 5 := by
    have hcop : (orderOf (a * x)).Coprime 2 := by rw [hax5]; norm_num
    rw [hcop.orderOf_pow, hax5]
  have h3ord : orderOf ((a * x) ^ 3) = 5 := by
    have hcop : (orderOf (a * x)).Coprime 3 := by rw [hax5]; norm_num
    rw [hcop.orderOf_pow, hax5]
  have hx_ne_as : x ≠ a * s := by
    intro hxas
    have hord : orderOf (a * x) = orderOf s := by
      rw [hxas, ← mul_assoc, ha2, one_mul]
    rw [hax5, hs_order] at hord
    norm_num at hord
  have hGxyz_card : Nat.card ↥(Gxyz a s x) = 20 := by
    obtain ⟨e⟩ := hx.2.2 s hs hsx
    have h2c : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card, h2c]
  rcases hCls.inv_two (a * s) has_order with hA | hB
  ·
    have hsmem : s ∈ orb2A a a := ⟨hs, hA⟩
    have hx_sBase : x ∈ sBase a s :=
      ⟨hx.1.1, by simpa [hxs_comm] using hA.trans hconj_as_xs, hx.1.2.1, hx_ne_as⟩
    obtain ⟨i, hi⟩ := (hT4.partition s hsmem).cover x hx_sBase
    fin_cases i
    · exfalso
      simp only [sSet, Set.mem_setOf_eq] at hi
      exact absurd ((orderOf_eq_of_isConj hi.2).symm.trans h.orderOf_a) (by rw [hax5]; norm_num)
    · exfalso
      simp only [sSet, Set.mem_setOf_eq] at hi
      exact absurd ((orderOf_eq_of_isConj hi.2).symm.trans h.orderOf_z) (by rw [hax5]; norm_num)
    · exfalso
      simp only [sSet, Set.mem_setOf_eq] at hi
      have hcontra : orderOf ((a * x) ^ 2) = 2 := by rw [hi.2, hs_order]
      rw [h2ord] at hcontra
      norm_num at hcontra
    · exfalso
      simp only [sSet, Set.mem_setOf_eq] at hi
      have hcontra : orderOf ((a * x) ^ 2) = 2 :=
        (orderOf_eq_of_isConj hi.2).symm.trans h.orderOf_z
      rw [h2ord] at hcontra
      norm_num at hcontra
    · exfalso
      simp only [sSet, Set.mem_setOf_eq] at hi
      exact absurd (hi.2.symm.trans hax5) (by norm_num)
    · exfalso
      simp only [sSet, Set.mem_setOf_eq] at hi
      have hcontra : orderOf ((a * x) ^ 3) = 2 := by rw [hi.2, hs_order]
      rw [h3ord] at hcontra
      norm_num at hcontra
  ·
    have hsmem : s ∈ orb2B a z a := ⟨hs, hB⟩
    have hx_tBase : x ∈ tBase a z s :=
      ⟨hx.1.1, by simpa [hxs_comm] using hB.trans hconj_as_xs, hx.1.2.1⟩
    obtain ⟨i, hi⟩ := (hT6.partition s hsmem).cover x hx_tBase
    fin_cases i
    · exfalso
      simp only [tSet, Set.mem_setOf_eq] at hi
      exact absurd ((orderOf_eq_of_isConj hi.2).symm.trans h.orderOf_a) (by rw [hax5]; norm_num)
    · exfalso
      simp only [tSet, Set.mem_setOf_eq] at hi
      exact absurd ((orderOf_eq_of_isConj hi.2).symm.trans h.orderOf_z) (by rw [hax5]; norm_num)
    · exfalso
      simp only [tSet, Set.mem_setOf_eq] at hi
      exact absurd (hi.2.symm.trans hax5) (by norm_num)
    · exfalso
      simp only [tSet, Set.mem_setOf_eq] at hi
      exact absurd (hi.2.1.symm.trans hax5) (by norm_num)
    · exfalso
      simp only [tSet, Set.mem_setOf_eq] at hi
      exact absurd (hi.2.1.symm.trans hax5) (by norm_num)
    ·
      exfalso
      have h240 : Nat.card ↥(Gxy a s ⊓ Gx x) = 240 := by
        simpa using hT6.card_stab s hsmem 5 x hi
      have h20 : Nat.card ↥(Gxy a s ⊓ Gx x) = 20 := by
        rw [← Gxyz_eq_inf a s x]
        exact hGxyz_card
      rw [h20] at h240
      norm_num at h240
    ·
      simp only [tSet, Set.mem_setOf_eq] at hi
      exact hi.2.2
    · exfalso
      simp only [tSet, Set.mem_setOf_eq] at hi
      exact absurd (hi.2.1.symm.trans hax5) (by norm_num)

end CFSG.EvenSporadicStandard.HNRecog.Section3
