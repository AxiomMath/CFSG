module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma y4_eq_inv_mul_of_mul_eq {Q : Type*} [Group Q] {a b c ε : Q}
    (h : a * b * c = ε) : c = (a * b)⁻¹ * ε := by
  calc c = (a * b)⁻¹ * (a * b * c) := by group
       _ = (a * b)⁻¹ * ε := by rw [h]

private lemma y4_inv_mul_eq {Q : Type*} [Group Q] {a b : Q}
    (ha : a * a = 1) (hb : b * b = 1) : (a * b)⁻¹ = b * a := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]

private lemma y4_mul_self_central {Q : Type*} [Group Q] {x ε : Q}
    (hε2 : ε * ε = 1) (hεC : ∀ z : Q, ε * z = z * ε) :
    (x * ε) * (x * ε) = x * x := by
  have hcomm : Commute x ε := (hεC x).symm
  calc (x * ε) * (x * ε) = (x * ε) ^ 2 := by rw [pow_two]
       _ = x ^ 2 * ε ^ 2 := hcomm.mul_pow 2
       _ = x * x := by rw [pow_two, pow_two, hε2, mul_one]

private lemma y4_commute_of_sq_one {Q : Type*} [Group Q] {a b : Q}
    (ha : a * a = 1) (hb : b * b = 1) (h : (b * a) * (b * a) = 1) :
    a * b = b * a := by
  have hbainv : (b * a)⁻¹ = b * a := inv_eq_of_mul_eq_one_right h
  calc a * b = a⁻¹ * b⁻¹ := by
        rw [inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
       _ = (b * a)⁻¹ := (mul_inv_rev b a).symm
       _ = b * a := hbainv

private lemma y4_commute_data {Q : Type*} [Group Q] {t a b c ε : Q}
    (ht : t * t = 1) (htc : ∀ x : Q, x * t = t * x)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hε : ε = 1 ∨ ε = t) (habc : a * b * c = ε) :
    Commute a b ∧ Commute a c ∧ Commute b c := by
  have hε2 : ε * ε = 1 := by
    rcases hε with rfl | rfl <;> simpa using ht
  have hεC : ∀ z : Q, ε * z = z * ε := by
    intro z
    rcases hε with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (htc z).symm
  have hab : Commute a b := y4_commute_of_sq_one ha hb (by
    have h := hc
    rw [y4_eq_inv_mul_of_mul_eq habc] at h
    rwa [y4_inv_mul_eq ha hb, y4_mul_self_central hε2 hεC] at h)
  have hc_f : c = (a * b) * ε := by
    rw [y4_eq_inv_mul_of_mul_eq habc, y4_inv_mul_eq ha hb, ← hab.eq]
  have hac : Commute a c := by
    have h : Commute a ((a * b) * ε) :=
      ((Commute.refl a).mul_right hab).mul_right ((hεC a).symm)
    rwa [← hc_f] at h
  have hbc : Commute b c := by
    have h : Commute b ((a * b) * ε) :=
      ((hab.symm).mul_right (Commute.refl b)).mul_right ((hεC b).symm)
    rwa [← hc_f] at h
  exact ⟨hab, hac, hbc⟩

private lemma y4_mul_self_eq_one_of_commute {Q : Type*} [Group Q] {x y : Q}
    (h : Commute x y) (hx : x * x = 1) (hy : y * y = 1) : (x * y) * (x * y) = 1 := by
  calc (x * y) * (x * y) = (x * y) ^ 2 := by rw [pow_two]
       _ = x ^ 2 * y ^ 2 := h.mul_pow 2
       _ = 1 := by rw [pow_two, pow_two, hx, hy, one_mul]

theorem y4_elemab_of_orbit {Q : Type*} [Group Q] {t a b c : Q}
    (ht : t * t = 1) (htc : ∀ x : Q, x * t = t * x)
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (habc : a * b * c = 1 ∨ a * b * c = t)
    (hall : ∀ x : Q, ∃ p : Q, (p = 1 ∨ p = t) ∧ (x = p ∨ x = p * a ∨ x = p * b ∨ x = p * c)) :
    ∀ x y : Q, x * y = y * x ∧ x * x = 1 := by
  have hcomm : Commute a b ∧ Commute a c ∧ Commute b c := by
    rcases habc with h1 | ht1
    · exact y4_commute_data ht htc ha hb hc (Or.inl rfl) h1
    · exact y4_commute_data ht htc ha hb hc (Or.inr rfl) ht1
  obtain ⟨hab, hac, hbc⟩ := hcomm
  let Base : Q → Prop := fun z => z = 1 ∨ z = a ∨ z = b ∨ z = c
  have hbase_sq : ∀ z, Base z → z * z = 1 := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [one_mul]
    · exact ha
    · exact hb
    · exact hc
  have hbase_comm : ∀ z w, Base z → Base w → Commute z w := by
    intro z w hz hw
    rcases hz with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      first
        | exact Commute.one_left _
        | exact Commute.one_right _
        | exact Commute.refl _
        | exact hab
        | exact hab.symm
        | exact hac
        | exact hac.symm
        | exact hbc
        | exact hbc.symm
  intro x y
  obtain ⟨p, hp, hx⟩ := hall x
  obtain ⟨p', hp', hy⟩ := hall y
  have hpz : ∀ z : Q, Commute p z := by
    intro z
    rcases hp with rfl | rfl
    · exact Commute.one_left z
    · exact (htc z).symm
  have hpz' : ∀ z : Q, Commute p' z := by
    intro z
    rcases hp' with rfl | rfl
    · exact Commute.one_left z
    · exact (htc z).symm
  obtain ⟨q, hqBase, hxq, hpq⟩ : ∃ q : Q, Base q ∧ x = p * q ∧ Commute p q := by
    rcases hx with hx1 | hx2 | hx3 | hx4
    · exact ⟨1, Or.inl rfl, by rw [hx1, mul_one], hpz 1⟩
    · exact ⟨a, Or.inr (Or.inl rfl), by rw [hx2], hpz a⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), by rw [hx3], hpz b⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inr rfl)), by rw [hx4], hpz c⟩
  obtain ⟨q', hq'Base, hyq', _⟩ : ∃ q' : Q, Base q' ∧ y = p' * q' ∧ Commute p' q' := by
    rcases hy with hy1 | hy2 | hy3 | hy4
    · exact ⟨1, Or.inl rfl, by rw [hy1, mul_one], hpz' 1⟩
    · exact ⟨a, Or.inr (Or.inl rfl), by rw [hy2], hpz' a⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl rfl)), by rw [hy3], hpz' b⟩
    · exact ⟨c, Or.inr (Or.inr (Or.inr rfl)), by rw [hy4], hpz' c⟩
  have hqq' : Commute q q' := hbase_comm q q' hqBase hq'Base
  have hcomm_xy : Commute (p * q) (p' * q') :=
    Commute.mul_left ((hpz p').mul_right (hpz q')) (((hpz' q).symm).mul_right hqq')
  have hp2 : p * p = 1 := by
    rcases hp with rfl | rfl
    · rw [one_mul]
    · exact ht
  refine ⟨?_, ?_⟩
  · rw [hxq, hyq']
    exact hcomm_xy
  · rw [hxq]
    exact y4_mul_self_eq_one_of_commute hpq hp2 (hbase_sq q hqBase)

end CFSG.OddStandard.HigherRank.YamadaG23
