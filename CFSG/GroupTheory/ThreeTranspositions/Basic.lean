module

public import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open Subgroup

@[expose] def HasE9 (X : Type*) [Group X] : Prop :=
  ∃ x y : X, orderOf x = 3 ∧ orderOf y = 3 ∧ Commute x y ∧ y ∉ Subgroup.zpowers x

theorem HasE9.map_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (h : HasE9 X) : HasE9 Y := by
  obtain ⟨x, y, hx, hy, hxy, hyx⟩ := h
  refine ⟨f x, f y, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective f hf x, hx]
  · rw [orderOf_injective f hf y, hy]
  · exact hxy.map f
  · intro hmem
    rw [← MonoidHom.map_zpowers f x] at hmem
    exact hyx ((Subgroup.mem_map_iff_mem hf).mp hmem)

theorem HasE9.two_le_pRank {X : Type*} [Group X] [Finite X] (h : HasE9 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨x, y, hx, hy, hxy, hyx⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.GroupTheory.two_le_pRank_of_commute (p := 3) (H := ⊤) (x := x) (y := y)
    (Subgroup.mem_top x) (Subgroup.mem_top y) hx hy hxy hyx

theorem orderOf_mul_eq_three_of_involutions {Q : Type*} [Group Q] {d e : Q}
    (hd : d ^ 2 = 1) (he : e ^ 2 = 1) (h3 : (d * e) ^ 3 = 1) (hne : d * e ≠ e * d) :
    orderOf (d * e) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime h3 ?_
  intro h1
  apply hne
  have hde1 : d = e⁻¹ := mul_eq_one_iff_eq_inv.mp h1
  rw [hde1, inv_mul_cancel, mul_inv_cancel]

theorem mul_mul_inv_eq_of_involutions {Q : Type*} [Group Q] {d e : Q}
    (hd : d ^ 2 = 1) (he : e ^ 2 = 1) (h3 : (d * e) ^ 3 = 1) :
    d * (d * e) * d⁻¹ = (d * e)⁻¹ ∧ (d * e) * d * (d * e)⁻¹ = e := by
  have hd2 : d * d = 1 := by simpa [pow_two] using hd
  have he2 : e * e = 1 := by simpa [pow_two] using he
  have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have h2 : (d * e) * (d * e) = (d * e)⁻¹ := by
    have hx : (d * e) ^ 2 * (d * e) = 1 := by simpa [pow_succ] using h3
    simpa [pow_two] using (mul_eq_one_iff_eq_inv.mp hx)
  constructor
  · rw [← mul_assoc d d e, hd2, one_mul, hd', mul_inv_rev, hd', he']
  · rw [mul_inv_rev, hd', he']
    calc (d * e) * d * (e * d) = ((d * e) * (d * e)) * d := by simp only [mul_assoc]
      _ = (d * e)⁻¹ * d := by rw [h2]
      _ = (e * d) * d := by rw [mul_inv_rev, hd', he']
      _ = e := by rw [mul_assoc, hd2, mul_one]

theorem hasE9_of_commuting_pairs {Q : Type*} [Group Q] {d e b c : Q}
    (hd : d ^ 2 = 1) (he : e ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hde : (d * e) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1)
    (hde' : d * e ≠ e * d) (hbc' : b * c ≠ c * b)
    (hdb : d * b = b * d) (hdc : d * c = c * d) (heb : e * b = b * e) (hec : e * c = c * e) :
    HasE9 Q := by
  have hx3 : orderOf (d * e) = 3 := orderOf_mul_eq_three_of_involutions hd he hde hde'
  have hy3 : orderOf (b * c) = 3 := orderOf_mul_eq_three_of_involutions hb hc hbc hbc'
  refine ⟨d * e, b * c, hx3, hy3, ?_, ?_⟩
  · exact (((commute_iff_eq d b).mpr hdb).mul_right ((commute_iff_eq d c).mpr hdc)).mul_left
      (((commute_iff_eq e b).mpr heb).mul_right ((commute_iff_eq e c).mpr hec))
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hdconj : d * (d * e) * d⁻¹ = (d * e)⁻¹ :=
      (mul_mul_inv_eq_of_involutions hd he hde).1
    have hdy : d * (b * c) * d⁻¹ = b * c := by
      have h : Commute d (b * c) :=
        ((commute_iff_eq d b).mpr hdb).mul_right ((commute_iff_eq d c).mpr hdc)
      rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : d * (d * e) ^ n * d⁻¹ = ((d * e)⁻¹) ^ n := by
      rw [← conj_zpow, hdconj]
    have h2 : d * (d * e) ^ n * d⁻¹ = b * c := by
      rw [hn, hdy]
    have hxinv : ((d * e)⁻¹) ^ n = (d * e) ^ n := by rw [← h1, h2, ← hn]
    have hxinv' : ((d * e) ^ n)⁻¹ = (d * e) ^ n := by rw [← inv_zpow, hxinv]
    have hyinv : (b * c)⁻¹ = b * c := by simpa [hn] using hxinv'
    have hy2 : (b * c) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [← hyinv]
      rw [mul_inv_cancel]
    have hdvd : orderOf (b * c) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
    rw [hy3] at hdvd
    norm_num at hdvd

theorem sq_or_cube_of_isConj {Q : Type*} [Group Q] {t : Q}
    (h : ∀ a : Q, (t * (a * t * a⁻¹)) ^ 2 = 1 ∨ (t * (a * t * a⁻¹)) ^ 3 = 1) {d e : Q}
    (hd : IsConj t d) (he : IsConj t e) : (d * e) ^ 2 = 1 ∨ (d * e) ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  obtain ⟨k, rfl⟩ := isConj_iff.mp he
  have hprod : (g * t * g⁻¹) * (k * t * k⁻¹) =
      g * (t * ((g⁻¹ * k) * t * (g⁻¹ * k)⁻¹)) * g⁻¹ := by
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
  rcases h (g⁻¹ * k) with h2 | h3
  · left
    rw [hprod, conj_pow, h2, mul_one, mul_inv_cancel]
  · right
    rw [hprod, conj_pow, h3, mul_one, mul_inv_cancel]

end CFSG.GroupTheory.ThreeTranspositions
