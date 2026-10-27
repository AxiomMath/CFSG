module

public import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
public import Mathlib.Tactic.Basify

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith

theorem finite_check_psl (q q' : ℕ) (hq : 2 ≤ q) (hq6 : q ≤ 6) (hq' : 2 ≤ q') (hq'6 : q' ≤ 6)
    (hne : q ≠ q') :
    Nat.gcd 3 (q' - 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ≠
      Nat.gcd 3 (q - 1) * (q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 - 1))) := by
  interval_cases q <;> interval_cases q' <;> first | exact absurd rfl hne | decide

theorem finite_check_psu (q q' : ℕ) (hq : 2 ≤ q) (hq6 : q ≤ 6) (hq' : 2 ≤ q') (hq'6 : q' ≤ 6)
    (hne : q ≠ q') :
    Nat.gcd 3 (q' + 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) ≠
      Nat.gcd 3 (q + 1) * (q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 + 1))) := by
  interval_cases q <;> interval_cases q' <;> first | exact absurd rfl hne | decide

theorem four_mul_sq_lt {n : ℕ} (h : 7 ≤ n) : 4 * (n + 2) ^ 2 < n ^ 3 := by
  have h1 : 7 * n ^ 2 ≤ n ^ 3 := by
    calc 7 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ h
      _ = n ^ 3 := by ring
  nlinarith

theorem le_six_of_bounds {q q' c : ℕ} (hq : 2 ≤ q) (hq' : 2 ≤ q') (hc : c ≤ 2)
    (h1 : q' ^ 3 ≤ 4 * (q + c) ^ 2) (h2 : q ^ 3 ≤ 4 * (q' + c) ^ 2) : q ≤ 6 ∧ q' ≤ 6 := by
  rcases le_total q q' with hle | hle
  · have : q' ≤ 6 := by
      by_contra hc'
      have h3 : (q + c) ^ 2 ≤ (q' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have := four_mul_sq_lt (n := q') (by omega)
      omega
    omega
  · have : q ≤ 6 := by
      by_contra hc'
      have h3 : (q' + c) ^ 2 ≤ (q + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have := four_mul_sq_lt (n := q) (by omega)
      omega
    omega

theorem prime_pow_ne_of_ne {p ℓ a b : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hb : 1 ≤ b)
    (hpl : p ≠ ℓ) : p ^ a ≠ ℓ ^ b := by
  intro h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : ℓ ^ b = 1 := by simpa using h.symm
    simp [hℓ.ne_one, show b ≠ 0 by omega] at this
  · have h1 : ℓ ∣ p ^ a := by rw [h]; exact dvd_pow_self ℓ (by omega)
    exact hpl ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 (hℓ.dvd_of_dvd_pow h1)).symm

theorem order_psl3_inj {p ℓ a b : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Nat.gcd 3 (ℓ ^ b - 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) =
      Nat.gcd 3 (p ^ a - 1) * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 - 1)))) :
    p ^ a = ℓ ^ b := by
  have hpa : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hlb : 2 ≤ ℓ ^ b := by
    have := Nat.one_lt_pow (by omega : b ≠ 0) hℓ.one_lt
    omega
  have hg1c : Nat.Coprime p (Nat.gcd 3 (p ^ a - 1)) :=
    coprime_of_not_dvd hp fun hh =>
      not_dvd_sub_one hp (by omega) (dvd_pow_self p (by omega))
        (hh.trans (Nat.gcd_dvd_right 3 _))
  have hg2c : Nat.Coprime ℓ (Nat.gcd 3 (ℓ ^ b - 1)) :=
    coprime_of_not_dvd hℓ fun hh =>
      not_dvd_sub_one hℓ (by omega) (dvd_pow_self ℓ (by omega))
        (hh.trans (Nat.gcd_dvd_right 3 _))
  by_cases hpl : p = ℓ
  · subst hpl
    have hE : Nat.Coprime p (Nat.gcd 3 (p ^ b - 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) :=
      Nat.Coprime.mul_right hg2c
        (Nat.Coprime.mul_right (cop_pow_sub hp ha 2 (by norm_num))
          (cop_pow_sub hp ha 3 (by norm_num)))
    have hF : Nat.Coprime p (Nat.gcd 3 (p ^ a - 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 - 1))) :=
      Nat.Coprime.mul_right hg1c
        (Nat.Coprime.mul_right (cop_pow_sub hp hb 2 (by norm_num))
          (cop_pow_sub hp hb 3 (by norm_num)))
    have h1 : p ^ (a * 3) * (Nat.gcd 3 (p ^ b - 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) =
        p ^ (b * 3) * (Nat.gcd 3 (p ^ a - 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 - 1))) := by
      calc _ = Nat.gcd 3 (p ^ b - 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) := by
            ring
        _ = Nat.gcd 3 (p ^ a - 1) * ((p ^ b) ^ 3 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 - 1))) := h
        _ = _ := by ring
    have hexp : a = b := by
      have := exp_eq_of_mul_eq hp hE hF h1
      omega
    rw [hexp]
  · exfalso
    have hcop : Nat.Coprime ((p ^ a) ^ 3) ((ℓ ^ b) ^ 3) :=
      Nat.Coprime.pow 3 3 (Nat.Coprime.pow a b ((Nat.coprime_primes hp hℓ).2 hpl))
    obtain ⟨x, hx⟩ : ∃ x, p ^ a = x + 1 := ⟨p ^ a - 1, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, ℓ ^ b = y + 1 := ⟨ℓ ^ b - 1, by omega⟩
    have hg1 : Nat.Coprime (p ^ a) (Nat.gcd 3 (p ^ a - 1)) := Nat.Coprime.pow_left a hg1c
    have hg2 : Nat.Coprime (ℓ ^ b) (Nat.gcd 3 (ℓ ^ b - 1)) := Nat.Coprime.pow_left b hg2c
    have hb1 : (ℓ ^ b) ^ 3 ≤ 4 * (p ^ a + 2) ^ 2 := by
      have hd : (ℓ ^ b) ^ 3 ∣
          Nat.gcd 3 (ℓ ^ b - 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1))) :=
        ⟨Nat.gcd 3 (p ^ a - 1) * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 - 1)), by rw [h]; ring⟩
      have hc : Nat.Coprime ((ℓ ^ b) ^ 3) (Nat.gcd 3 (ℓ ^ b - 1) * (p ^ a) ^ 3) :=
        Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg2) hcop.symm
      have hE : (ℓ ^ b) ^ 3 ∣ ((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1) :=
        hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
      rw [hx] at hE
      have e1 : (x + 1) ^ 2 - 1 = x * (x + 2) := Nat.sub_eq_of_eq_add (by ring)
      have e2 : (x + 1) ^ 3 - 1 = x * (x ^ 2 + 3 * x + 3) := Nat.sub_eq_of_eq_add (by ring)
      have e : ((x + 1) ^ 2 - 1) * ((x + 1) ^ 3 - 1) =
          x ^ 2 * ((x + 2) * (x ^ 2 + 3 * x + 3)) := by
        rw [e1, e2]; ring
      rw [e] at hE
      have hx0 : 0 < x := by omega
      have := bndZ (ℓ := ℓ) (k := b * 3) (t := x) (a := x) (b := x + 2) hℓ hx0
        (Or.inl ⟨rfl, rfl⟩) (by rw [pow_mul]; exact hE)
      calc (ℓ ^ b) ^ 3 = ℓ ^ (b * 3) := (pow_mul ℓ b 3).symm
        _ ≤ 4 * (x + 3) ^ 2 := this
        _ = 4 * (p ^ a + 2) ^ 2 := by rw [hx]
    have hb2 : (p ^ a) ^ 3 ≤ 4 * (ℓ ^ b + 2) ^ 2 := by
      have hd : (p ^ a) ^ 3 ∣
          Nat.gcd 3 (p ^ a - 1) * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 - 1))) :=
        ⟨Nat.gcd 3 (ℓ ^ b - 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 - 1)), by rw [← h]; ring⟩
      have hc : Nat.Coprime ((p ^ a) ^ 3) (Nat.gcd 3 (p ^ a - 1) * (ℓ ^ b) ^ 3) :=
        Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg1) hcop
      have hE : (p ^ a) ^ 3 ∣ ((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 - 1) :=
        hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
      rw [hy] at hE
      have e1 : (y + 1) ^ 2 - 1 = y * (y + 2) := Nat.sub_eq_of_eq_add (by ring)
      have e2 : (y + 1) ^ 3 - 1 = y * (y ^ 2 + 3 * y + 3) := Nat.sub_eq_of_eq_add (by ring)
      have e : ((y + 1) ^ 2 - 1) * ((y + 1) ^ 3 - 1) =
          y ^ 2 * ((y + 2) * (y ^ 2 + 3 * y + 3)) := by
        rw [e1, e2]; ring
      rw [e] at hE
      have hy0 : 0 < y := by omega
      have := bndZ (ℓ := p) (k := a * 3) (t := y) (a := y) (b := y + 2) hp hy0
        (Or.inl ⟨rfl, rfl⟩) (by rw [pow_mul]; exact hE)
      calc (p ^ a) ^ 3 = p ^ (a * 3) := (pow_mul p a 3).symm
        _ ≤ 4 * (y + 3) ^ 2 := this
        _ = 4 * (ℓ ^ b + 2) ^ 2 := by rw [hy]
    obtain ⟨h6, h6'⟩ := le_six_of_bounds hpa hlb (le_refl 2) hb1 hb2
    exact finite_check_psl (p ^ a) (ℓ ^ b) hpa h6 hlb h6' (prime_pow_ne_of_ne hp hℓ hb hpl) h

theorem order_psu3_inj {p ℓ a b : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Nat.gcd 3 (ℓ ^ b + 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) =
      Nat.gcd 3 (p ^ a + 1) * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1)))) :
    p ^ a = ℓ ^ b := by
  have hpa : 2 ≤ p ^ a := by
    have := Nat.one_lt_pow (by omega : a ≠ 0) hp.one_lt
    omega
  have hlb : 2 ≤ ℓ ^ b := by
    have := Nat.one_lt_pow (by omega : b ≠ 0) hℓ.one_lt
    omega
  have hg1c : Nat.Coprime p (Nat.gcd 3 (p ^ a + 1)) :=
    coprime_of_not_dvd hp fun hh =>
      not_dvd_add_one hp (dvd_pow_self p (by omega)) (hh.trans (Nat.gcd_dvd_right 3 _))
  have hg2c : Nat.Coprime ℓ (Nat.gcd 3 (ℓ ^ b + 1)) :=
    coprime_of_not_dvd hℓ fun hh =>
      not_dvd_add_one hℓ (dvd_pow_self ℓ (by omega)) (hh.trans (Nat.gcd_dvd_right 3 _))
  by_cases hpl : p = ℓ
  · subst hpl
    have hE : Nat.Coprime p (Nat.gcd 3 (p ^ b + 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) :=
      Nat.Coprime.mul_right hg2c
        (Nat.Coprime.mul_right (cop_pow_sub hp ha 2 (by norm_num))
          (cop_pow_add hp ha 3 (by norm_num)))
    have hF : Nat.Coprime p (Nat.gcd 3 (p ^ a + 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) :=
      Nat.Coprime.mul_right hg1c
        (Nat.Coprime.mul_right (cop_pow_sub hp hb 2 (by norm_num))
          (cop_pow_add hp hb 3 (by norm_num)))
    have h1 : p ^ (a * 3) * (Nat.gcd 3 (p ^ b + 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) =
        p ^ (b * 3) * (Nat.gcd 3 (p ^ a + 1) * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) := by
      calc _ = Nat.gcd 3 (p ^ b + 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) := by
            ring
        _ = Nat.gcd 3 (p ^ a + 1) * ((p ^ b) ^ 3 * (((p ^ b) ^ 2 - 1) * ((p ^ b) ^ 3 + 1))) := h
        _ = _ := by ring
    have hexp : a = b := by
      have := exp_eq_of_mul_eq hp hE hF h1
      omega
    rw [hexp]
  · exfalso
    have hcop : Nat.Coprime ((p ^ a) ^ 3) ((ℓ ^ b) ^ 3) :=
      Nat.Coprime.pow 3 3 (Nat.Coprime.pow a b ((Nat.coprime_primes hp hℓ).2 hpl))
    obtain ⟨x, hx⟩ : ∃ x, p ^ a = x + 2 := ⟨p ^ a - 2, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, ℓ ^ b = y + 2 := ⟨ℓ ^ b - 2, by omega⟩
    have hg1 : Nat.Coprime (p ^ a) (Nat.gcd 3 (p ^ a + 1)) := Nat.Coprime.pow_left a hg1c
    have hg2 : Nat.Coprime (ℓ ^ b) (Nat.gcd 3 (ℓ ^ b + 1)) := Nat.Coprime.pow_left b hg2c
    have hb1 : (ℓ ^ b) ^ 3 ≤ 4 * (p ^ a + 1) ^ 2 := by
      have hd : (ℓ ^ b) ^ 3 ∣
          Nat.gcd 3 (ℓ ^ b + 1) * ((p ^ a) ^ 3 * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1))) :=
        ⟨Nat.gcd 3 (p ^ a + 1) * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1)), by rw [h]; ring⟩
      have hc : Nat.Coprime ((ℓ ^ b) ^ 3) (Nat.gcd 3 (ℓ ^ b + 1) * (p ^ a) ^ 3) :=
        Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg2) hcop.symm
      have hE : (ℓ ^ b) ^ 3 ∣ ((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1) :=
        hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
      rw [hx] at hE
      have e1 : (x + 2) ^ 2 - 1 = (x + 1) * (x + 3) := Nat.sub_eq_of_eq_add (by ring)
      have e : ((x + 2) ^ 2 - 1) * ((x + 2) ^ 3 + 1) =
          (x + 3) ^ 2 * ((x + 1) * (x ^ 2 + 3 * x + 3)) := by
        rw [e1]; ring
      rw [e] at hE
      have := bndZ (ℓ := ℓ) (k := b * 3) (t := x) (a := x + 3) (b := x + 1) hℓ (by omega)
        (Or.inr ⟨rfl, rfl⟩) (by rw [pow_mul]; exact hE)
      calc (ℓ ^ b) ^ 3 = ℓ ^ (b * 3) := (pow_mul ℓ b 3).symm
        _ ≤ 4 * (x + 3) ^ 2 := this
        _ = 4 * (p ^ a + 1) ^ 2 := by rw [hx]
    have hb2 : (p ^ a) ^ 3 ≤ 4 * (ℓ ^ b + 1) ^ 2 := by
      have hd : (p ^ a) ^ 3 ∣
          Nat.gcd 3 (p ^ a + 1) * ((ℓ ^ b) ^ 3 * (((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1))) :=
        ⟨Nat.gcd 3 (ℓ ^ b + 1) * (((p ^ a) ^ 2 - 1) * ((p ^ a) ^ 3 + 1)), by rw [← h]; ring⟩
      have hc : Nat.Coprime ((p ^ a) ^ 3) (Nat.gcd 3 (p ^ a + 1) * (ℓ ^ b) ^ 3) :=
        Nat.Coprime.mul_right (Nat.Coprime.pow_left 3 hg1) hcop
      have hE : (p ^ a) ^ 3 ∣ ((ℓ ^ b) ^ 2 - 1) * ((ℓ ^ b) ^ 3 + 1) :=
        hc.dvd_of_dvd_mul_left (by rwa [← mul_assoc] at hd)
      rw [hy] at hE
      have e1 : (y + 2) ^ 2 - 1 = (y + 1) * (y + 3) := Nat.sub_eq_of_eq_add (by ring)
      have e : ((y + 2) ^ 2 - 1) * ((y + 2) ^ 3 + 1) =
          (y + 3) ^ 2 * ((y + 1) * (y ^ 2 + 3 * y + 3)) := by
        rw [e1]; ring
      rw [e] at hE
      have := bndZ (ℓ := p) (k := a * 3) (t := y) (a := y + 3) (b := y + 1) hp (by omega)
        (Or.inr ⟨rfl, rfl⟩) (by rw [pow_mul]; exact hE)
      calc (p ^ a) ^ 3 = p ^ (a * 3) := (pow_mul p a 3).symm
        _ ≤ 4 * (y + 3) ^ 2 := this
        _ = 4 * (ℓ ^ b + 1) ^ 2 := by rw [hy]
    obtain ⟨h6, h6'⟩ := le_six_of_bounds hpa hlb (by norm_num : 1 ≤ 2) hb1 hb2
    exact finite_check_psu (p ^ a) (ℓ ^ b) hpa h6 hlb h6' (prime_pow_ne_of_ne hp hℓ hb hpl) h

end CFSG.HardMathSupport.Solomon.Coordinator
