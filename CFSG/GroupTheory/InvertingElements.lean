module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GroupTheory

theorem pow_odd_inverts {G : Type*} [Group G] {t y : G} (h : t * y * t⁻¹ = y⁻¹) {m : ℕ}
    (hm : Odd m) : t ^ m * y * (t ^ m)⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := hm
  have h2 : t ^ 2 * y * (t ^ 2)⁻¹ = y := by
    have : t ^ 2 * y * (t ^ 2)⁻¹ = t * (t * y * t⁻¹) * t⁻¹ := by rw [pow_two]; group
    rw [this, h]
    have : t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ := by group
    rw [this, h, inv_inv]
  have h2' : Commute (t ^ 2) y := by
    show t ^ 2 * y = y * t ^ 2
    have := h2
    calc t ^ 2 * y = t ^ 2 * y * (t ^ 2)⁻¹ * t ^ 2 := by group
      _ = y * t ^ 2 := by rw [this]
  have h3 : Commute (t ^ (2 * k)) y := by
    rw [pow_mul]; exact h2'.pow_left k
  have : t ^ (2 * k + 1) * y * (t ^ (2 * k + 1))⁻¹ =
      t ^ (2 * k) * (t * y * t⁻¹) * (t ^ (2 * k))⁻¹ := by group
  rw [this, h]
  have h4 : Commute (t ^ (2 * k)) y⁻¹ := h3.inv_right
  rw [h4.eq]
  group

private theorem commute_of_sq_commute {G : Type*} [Group G] {u a : G}
    (hu : Odd (orderOf u)) (h : u ^ 2 * a = a * u ^ 2) : u * a = a * u := by
  have hmem : u ∈ Subgroup.zpowers (u ^ 2) :=
    mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr hu)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hc : Commute (u ^ 2) a := h
  have := (hc.zpow_left m).eq
  rwa [hm] at this

private theorem commute_of_inverted {G : Type*} [Group G] {t u a : G}
    (hu : Odd (orderOf u)) (hinv : t * u * t⁻¹ = u⁻¹)
    (ha : t * a = a * t) (hua : t * (u * a * u⁻¹) = (u * a * u⁻¹) * t) :
    u * a = a * u := by
  have hta : t * a * t⁻¹ = a := by rw [ha, mul_inv_cancel_right]
  have htua : t * (u * a * u⁻¹) * t⁻¹ = u * a * u⁻¹ := by rw [hua, mul_inv_cancel_right]
  have hconj : t * (u * a * u⁻¹) * t⁻¹ = u⁻¹ * a * u := by
    calc t * (u * a * u⁻¹) * t⁻¹ =
        (t * u * t⁻¹) * (t * a * t⁻¹) * (t * u * t⁻¹)⁻¹ := by group
      _ = u⁻¹ * a * u := by rw [hinv, hta, inv_inv]
  have key : u ^ 2 * a = a * u ^ 2 := by
    have e : u * a * u⁻¹ = u⁻¹ * a * u := htua.symm.trans hconj
    rw [pow_two]
    calc u * u * a = u * (u * a * u⁻¹) * u := by group
      _ = u * (u⁻¹ * a * u) * u := by rw [e]
      _ = a * (u * u) := by group
  exact commute_of_sq_commute hu key

theorem mem_centralizer_of_inverted {G : Type*} [Group G] {t u : G} {A : Subgroup G}
    (hu : Odd (orderOf u)) (hinv : t * u * t⁻¹ = u⁻¹) (hA : ∀ a ∈ A, t * a = a * t)
    (huA : u ∈ Subgroup.normalizer (A : Set G)) :
    u ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hua : u * a * u⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp huA a).mp ha
  exact (commute_of_inverted hu hinv (hA a ha) (hA _ hua)).symm

theorem exists_prime_pow_orderOf_not_mem {G : Type*} [Group G] {B H : Subgroup G}
    (hodd : ∀ b ∈ B, Odd (orderOf b)) {b : G} (hb : b ∈ B) (hbH : b ∉ H) :
    ∃ b' ∈ B, b' ∉ H ∧ ∃ r e : ℕ, r.Prime ∧ r ≠ 2 ∧ orderOf b' = r ^ e := by
  suffices key : ∀ n : ℕ, ∀ b : G, orderOf b = n → b ∈ B → b ∉ H →
      ∃ b' ∈ B, b' ∉ H ∧ ∃ r e : ℕ, r.Prime ∧ r ≠ 2 ∧ orderOf b' = r ^ e from
    key _ b rfl hb hbH
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hbn hb hbH
    have hn0 : n ≠ 0 := by rw [← hbn]; exact (hodd b hb).pos.ne'
    have hn1 : n ≠ 1 := by
      intro h1
      apply hbH
      have hb1 : b = 1 := by rw [← orderOf_eq_one_iff, hbn, h1]
      simpa [hb1] using (Subgroup.one_mem H)
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.one_lt.ne'
    by_cases hm1 : m = 1
    · have hne : n = p ^ e := by rw [he, hm1, mul_one]
      have hp2 : p ≠ 2 := by
        rcases hp.eq_two_or_odd' with hp2 | hpo
        · exfalso
          have hne2 : n = 2 ^ e := by rw [hne, hp2]
          have he0 : e = 0 := by
            by_contra he0
            have h2dvd : 2 ∣ n := by
              rw [hne2]
              obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
              rw [pow_succ]
              exact dvd_mul_left 2 _
            have hnodd : Odd n := by rw [← hbn]; exact hodd b hb
            exact (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr h2dvd)
          rw [he0, pow_zero] at hne2
          exact hn1 hne2
        · obtain ⟨k, hk⟩ := hpo
          omega
      refine ⟨b, hb, hbH, p, e, hp, hp2, ?_⟩
      rw [hbn, hne]
    · have hm0 : m ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at he
        exact hn0 he
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hm_gt1 : 1 < m := by omega
      have hpe_pos : 0 < p ^ e := pow_pos hp.pos e
      have hepos : 0 < e := by
        by_contra h0
        have he0 : e = 0 := by omega
        have hpdvd : p ∣ n := Nat.minFac_dvd n
        rw [he, he0, pow_zero, one_mul] at hpdvd
        exact hm hpdvd
      have hpe_gt1 : 1 < p ^ e := Nat.one_lt_pow hepos.ne' hp.one_lt
      have hult : p ^ e < n := by
        rw [he]
        calc p ^ e = p ^ e * 1 := (mul_one _).symm
          _ < p ^ e * m := Nat.mul_lt_mul_of_pos_left hm_gt1 hpe_pos
      have hvlt : m < n := by
        rw [he]
        calc m = 1 * m := (one_mul m).symm
          _ < p ^ e * m := Nat.mul_lt_mul_of_pos_right hpe_gt1 hmpos
      have hcop : Nat.Coprime (p ^ e) m :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
      have hbu_ord : orderOf (b ^ (p ^ e)) = m := by
        rw [orderOf_pow_of_dvd (pow_ne_zero e hp.ne_zero)
          (by rw [hbn, he]; exact dvd_mul_right (p ^ e) m), hbn, he,
          Nat.mul_div_cancel_left _ hpe_pos]
      have hbv_ord : orderOf (b ^ m) = p ^ e := by
        rw [orderOf_pow_of_dvd hm0 (by rw [hbn, he]; exact dvd_mul_left m (p ^ e)),
          hbn, he, Nat.mul_div_cancel _ hmpos]
      by_cases hbu : b ^ (p ^ e) ∈ H
      · have hbv_not : b ^ m ∉ H := by
          intro hbv
          apply hbH
          have hbez := Nat.gcd_eq_gcd_ab (p ^ e) m
          rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
          have hb_eq : b = (b ^ (p ^ e)) ^ (Nat.gcdA (p ^ e) m : ℤ) *
              (b ^ m) ^ (Nat.gcdB (p ^ e) m : ℤ) := by
            rw [← zpow_natCast b (p ^ e), ← zpow_natCast b m, ← zpow_mul, ← zpow_mul,
              ← zpow_add, ← hbez, zpow_one]
          rw [hb_eq]
          exact H.mul_mem (H.zpow_mem hbu _) (H.zpow_mem hbv _)
        exact ih (p ^ e) hult (b ^ m) hbv_ord (B.pow_mem hb m) hbv_not
      · exact ih m hvlt (b ^ (p ^ e)) hbu_ord (B.pow_mem hb _) hbu

end CFSG.GroupTheory
