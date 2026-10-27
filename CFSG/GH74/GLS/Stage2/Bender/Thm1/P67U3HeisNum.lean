module

import CFSG.GH74.GLS.Stage2.OddAut.HeisField
import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial

theorem u3hn_two_ne_zero {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp5 : 5 ≤ p) : (2 : K) ≠ 0 := by
  have := h.charP
  intro h20
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h20
  rw [CharP.cast_eq_zero_iff K p] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem u3hn_no_nine {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hd : p ^ f + 1 ∣ 9) : False := by
  have hle : p ^ f + 1 ≤ 9 := Nat.le_of_dvd (by norm_num) hd
  have h5 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  obtain ⟨c, hc⟩ : ∃ c, c = p ^ f := ⟨_, rfl⟩
  rw [← hc] at hd hle h5
  have h8 : c = 8 := by
    have h5c : 5 ≤ c := by omega
    have h8c : c ≤ 8 := by omega
    interval_cases c <;> first | rfl | (exfalso; revert hd; decide)
  have hpd : p ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = p ^ f by omega]
    exact dvd_pow_self p (by omega)
  have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow hpd)
  omega

theorem u3hn_fix {K : Type} [Field K] (τ : K ≃+* K) {t : ℕ} (hτ : orderOf τ = t) (ht : Odd t)
    {w : K} (hw : τ (τ w) = w) : τ w = w := by
  obtain ⟨k, rfl⟩ := ht
  have h1 : (τ ^ 2) ^ (k + 1) = τ := by
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hτ,
      pow_orderOf_eq_one, one_mul]
  have h2 : ∀ n : ℕ, ((τ ^ 2) ^ n) w = w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', RingAut.mul_apply, ih, sq, RingAut.mul_apply]
      exact hw
  have := h2 (k + 1)
  rw [h1] at this
  exact this

theorem u3hn_fixed_false {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hp5 : 5 ≤ p) {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2)
    (ht3 : t ≠ 3) (τ : K ≃+* K) (hτ : orderOf τ = t) {w : K} (hw0 : w ≠ 0) (hwτ : τ w = w)
    (hord : 3 * orderOf w = p ^ f + 1) : False := by
  obtain ⟨hdvd, hcard, -⟩ := CFSG.RankThree.UnitaryDescent.fixed_field_facts h ht ht2 τ hτ
  have hf1 : 1 ≤ f := h.one_le
  have := Fintype.ofFinite
    (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield τ)
  let w' : CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield τ :=
    ⟨w, RingHom.mem_eqLocusField.mpr hwτ⟩
  have hw'0 : w' ≠ 0 := fun h0 => hw0 (congrArg Subtype.val h0)
  have hpow := FiniteField.pow_card_sub_one_eq_one w' hw'0
  rw [← Nat.card_eq_fintype_card, hcard] at hpow
  have hpow' : w ^ ((p ^ (f / t)) ^ 2 - 1) = 1 := congrArg Subtype.val hpow
  have hht : f / t ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) ht.pos
    omega
  have hT5 : 5 ≤ p ^ (f / t) := hp5.trans (Nat.le_self_pow hht p)
  have ht5 : 5 ≤ t := by
    have h2 := ht.two_le
    by_contra hlt
    have h4 : t = 4 := by omega
    subst h4
    norm_num at ht
  have hq : p ^ f = (p ^ (f / t)) ^ t := by
    rw [← pow_mul, Nat.div_mul_cancel hdvd]
  have hdvd' := orderOf_dvd_of_pow_eq_one hpow'
  generalize p ^ (f / t) = T at hT5 hdvd' hq
  have h25 : 25 ≤ T ^ 2 := by
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ T ^ 2 := Nat.pow_le_pow_left hT5 2
  have hle : orderOf w ≤ T ^ 2 - 1 := Nat.le_of_dvd (by omega) hdvd'
  have hq5 : T ^ 5 ≤ T ^ t := Nat.pow_le_pow_right (by omega) ht5
  have h125 : 125 ≤ T ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ T ^ 3 := Nat.pow_le_pow_left hT5 3
  have hmul : 125 * T ^ 2 ≤ T ^ 3 * T ^ 2 := Nat.mul_le_mul_right _ h125
  have h5eq : T ^ 5 = T ^ 3 * T ^ 2 := by ring
  rw [hq] at hord
  omega

theorem u3_heis_torus_contra {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hp5 : 5 ≤ p) (h3 : 3 ∣ p ^ f + 1) {t : ℕ} (ht : t.Prime)
    (ht2 : t ≠ 2) (ht3 : t ≠ 3) (τ : K ≃+* K) (hτ : orderOf τ = t) (s : Kˣ)
    (hs : orderOf s = p ^ f + 1) (X : GL (Fin 3) K) (lam : K)
    (hmat : (X : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![τ (s : K) ^ 3, (τ (s : K) ^ 3)⁻¹, 1] *
        ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lam • diagonal ![(s : K) ^ 3, ((s : K) ^ 3)⁻¹, 1]) : False := by
  have hpp : p.Prime := h.prime
  have hf1 : 1 ≤ f := h.one_le
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hw0 : (s : K) ^ 3 ≠ 0 := pow_ne_zero 3 hs0
  have hsq : (s : K) ^ (p ^ f + 1) = 1 := by
    have h1 := pow_orderOf_eq_one s
    rw [hs] at h1
    simpa using congrArg Units.val h1
  have hso : orderOf (s : K) = p ^ f + 1 := by rw [orderOf_units, hs]
  have hord : 3 * orderOf ((s : K) ^ 3) = p ^ f + 1 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hso]; exact h3), hso]
    exact Nat.mul_div_cancel' h3
  rcases CFSG.GH74.GLS.Stage2.OddAut.trace_argument (u3hn_two_ne_zero h hp5) τ hs0 X lam hmat
    with h6 | h1 | h2
  · have h9 : (s : K) ^ 9 = 1 := by
      linear_combination ((s : K) ^ 3 - 1) * h6
    have hd : p ^ f + 1 ∣ 9 := by
      rw [← hs]
      exact orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using h9))
    exact u3hn_no_nine hpp hp5 hf1 hd
  · exact u3hn_fixed_false h hp5 ht ht2 ht3 τ hτ hw0 (by rw [map_pow]; exact h1) hord
  · have hwq : ((s : K) ^ 3) ^ (p ^ f + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hsq, one_pow]
    have hbar : h.bar ((s : K) ^ 3) = ((s : K) ^ 3)⁻¹ := by
      rw [h.bar_apply]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hwq
    have hτw : τ ((s : K) ^ 3) = h.bar ((s : K) ^ 3) := by
      rw [hbar, map_pow]
      exact eq_inv_of_mul_eq_one_left h2
    have hcomm : ∀ x : K, τ (h.bar x) = h.bar (τ x) := by
      intro x
      simp only [h.bar_apply, map_pow]
    have hττ : τ (τ ((s : K) ^ 3)) = (s : K) ^ 3 := by
      rw [hτw, hcomm, hτw, h.bar_bar]
    exact u3hn_fixed_false h hp5 ht ht2 ht3 τ hτ hw0
      (u3hn_fix τ hτ (ht.eq_two_or_odd'.resolve_left ht2) hττ) hord

end CFSG.GH74.GLS.Stage2.Bender.Thm1
