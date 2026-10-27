module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Num
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem not_pow_dvd_factorial_eleven {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 5 ≤ a) :
    ¬ p ^ a ∣ Nat.factorial 11 := by
  intro h
  have h5 : p ^ 5 ∣ Nat.factorial 11 := (pow_dvd_pow p ha).trans h
  have h2 : Nat.factorial 11 = 39916800 := by decide
  rw [h2] at h5
  have hle : p ^ 5 ≤ 39916800 := Nat.le_of_dvd (by norm_num) h5
  have hp34 : p ≤ 34 := by
    by_contra hcon
    have : 35 ≤ p := by omega
    have h1 : 35 ^ 5 ≤ p ^ 5 := Nat.pow_le_pow_left this 5
    norm_num at h1
    omega
  have key : ∀ p : ℕ, p ≤ 34 → p.Prime → p ≠ 2 → ¬ p ^ 5 ∣ 39916800 := by
    intro p hp34
    interval_cases p <;> norm_num
  exact key p hp34 hp hp2 h5

theorem pow_le_succ_of_dvd {p ℓ m a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hm : 1 ≤ m)
    (hr5 : 5 ≤ ℓ ^ m) (hdvd : p ^ a ∣ ℓ ^ m * ((ℓ ^ m) ^ 2 - 1)) : p ^ a ≤ ℓ ^ m + 1 := by
  set r := ℓ ^ m with hr
  have hfac : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    have : r ^ 2 = (r - 1) * (r + 1) + 1 := by
      obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      rw [hs]
      simp only [Nat.add_sub_cancel]
      ring
    omega
  by_cases hpl : p = ℓ
  ·
    subst hpl
    have hcop : Nat.Coprime (p ^ a) (r ^ 2 - 1) := by
      refine Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
      have h1 : p ∣ r ^ 2 := by
        rw [hr, ← pow_mul]
        exact dvd_pow_self p (by omega)
      have h2 : p ∣ r ^ 2 - (r ^ 2 - 1) := Nat.dvd_sub h1 hd
      have h3 : r ^ 2 - (r ^ 2 - 1) = 1 := by
        have : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      rw [h3] at h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    have h4 : p ^ a ∣ r := hcop.dvd_of_dvd_mul_right hdvd
    exact (Nat.le_of_dvd (by omega) h4).trans (Nat.le_succ r)
  ·
    have hcr : Nat.Coprime (p ^ a) r := by
      refine Nat.Coprime.pow_left a (Nat.Coprime.pow_right m ((Nat.coprime_primes hp hℓ).2 hpl))
    have h1 : p ^ a ∣ (r - 1) * (r + 1) := by
      have := hcr.dvd_of_dvd_mul_left hdvd
      rwa [hfac] at this
    by_cases hd1 : p ∣ r - 1
    · have hn : ¬ p ∣ r + 1 := by
        intro hd2
        have h2 : p ∣ (r + 1) - (r - 1) := Nat.dvd_sub hd2 hd1
        have h3 : (r + 1) - (r - 1) = 2 := by omega
        rw [h3] at h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
      have hc2 : Nat.Coprime (p ^ a) (r + 1) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
      have h4 : p ^ a ∣ r - 1 := hc2.dvd_of_dvd_mul_right h1
      exact (Nat.le_of_dvd (by omega) h4).trans (by omega)
    · have hc2 : Nat.Coprime (p ^ a) (r - 1) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hd1)
      have h4 : p ^ a ∣ r + 1 := hc2.dvd_of_dvd_mul_left h1
      exact Nat.le_of_dvd (by omega) h4

theorem not_isL2_of_pow_dvd {T : Type} [Group T] [Finite T] {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hdvd : ℓ ^ a ∣ Nat.card T) (hlt : 2 * Nat.card T < ℓ ^ a * (ℓ ^ a - 1) * (ℓ ^ a - 2)) :
    ¬ IVK.IsL2 T (fun r => Odd r ∧ 5 ≤ r) := by
  rintro ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩
  have hc := P27.Psp4Stage1.card_L2_mul_two (F := F) hodd
  rw [← Nat.card_congr e.toEquiv] at hc
  have : Fintype F := Fintype.ofFinite F
  have hprime : (ringChar F).Prime := CharP.char_is_prime F _
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, -, hFn0⟩ := FiniteField.card F (ringChar F)
  have hFn : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hFn0
  set r := Nat.card F with hr
  have hdvd' : ℓ ^ a ∣ r * (r ^ 2 - 1) := by
    rw [← hc]
    exact Dvd.dvd.mul_right hdvd 2
  have hle : ℓ ^ a ≤ r + 1 := by
    rw [hFn] at hdvd' h5 ⊢
    exact pow_le_succ_of_dvd hℓ hℓ2 hprime (by exact n.pos) h5 hdvd'
  have hx3 : 3 ≤ ℓ ^ a := by
    by_contra hcon
    have h1 : ℓ ^ a ≤ 2 := by omega
    have h2 : 2 ≤ ℓ := hℓ.two_le
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0
      simp at hlt
    · have : ℓ ≤ ℓ ^ a := Nat.le_self_pow (by omega) ℓ
      have : ℓ = 2 := by omega
      exact hℓ2 this
  have hge : ℓ ^ a - 1 ≤ r := by omega
  have h1 : (ℓ ^ a - 1) * (ℓ ^ a - 2) * ℓ ^ a ≤ r * (r - 1) * (r + 1) := by
    have e1 : ℓ ^ a - 2 ≤ r - 1 := by omega
    have e2 : ℓ ^ a ≤ r + 1 := hle
    exact Nat.mul_le_mul (Nat.mul_le_mul hge e1) e2
  have h2 : r * (r ^ 2 - 1) = r * (r - 1) * (r + 1) := by
    have hfac : r ^ 2 - 1 = (r - 1) * (r + 1) := by
      have : r ^ 2 = (r - 1) * (r + 1) + 1 := by
        obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
        rw [hs]
        simp only [Nat.add_sub_cancel]
        ring
      omega
    rw [hfac]
    ring
  have h3 : ℓ ^ a * (ℓ ^ a - 1) * (ℓ ^ a - 2) ≤ 2 * Nat.card T := by
    calc ℓ ^ a * (ℓ ^ a - 1) * (ℓ ^ a - 2) = (ℓ ^ a - 1) * (ℓ ^ a - 2) * ℓ ^ a := by ring
      _ ≤ r * (r - 1) * (r + 1) := h1
      _ = r * (r ^ 2 - 1) := h2.symm
      _ = Nat.card T * 2 := hc.symm
      _ = 2 * Nat.card T := by ring
  omega

theorem bad_of_pow_dvd {T : Type} [Group T] [Finite T] {ℓ a : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (ha : 5 ≤ a) (hdvd : ℓ ^ a ∣ Nat.card T)
    (hlt : 2 * Nat.card T < ℓ ^ a * (ℓ ^ a - 1) * (ℓ ^ a - 2)) : ∀ k : Kind, ¬ KindFactor k T := by
  intro k h
  have hL2 := not_isL2_of_pow_dvd hℓ hℓ2 hdvd hlt
  have h11 : ¬ Nat.card T ∣ Nat.factorial 11 := fun hd =>
    not_pow_dvd_factorial_eleven hℓ hℓ2 ha (hdvd.trans hd)
  cases k with
  | g2 => exact hL2 h
  | psp4 => exact hL2 h
  | l4 ε => exact hL2 h
  | m12 => exact h
  | mcl => exact h11 ((KindFactor.all h).card_dvd (Or.inl rfl))
  | ly => exact h11 ((KindFactor.all h).card_dvd (Or.inr rfl))

theorem quad_ineq {q : ℕ} (hq : 3 ≤ q) :
    2 * (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)) < q ^ 6 * (q ^ 6 - 1) * (q ^ 6 - 2) := by
  have hu : 9 ≤ q ^ 2 := by nlinarith
  have hw : 9 * q ^ 2 ≤ q ^ 6 := by
    have h1 : q ^ 6 = q ^ 2 * (q ^ 2 * q ^ 2) := by ring
    rw [h1]
    nlinarith
  have hApos : 0 < q ^ 6 * (q ^ 6 - 1) := by
    have : 729 ≤ q ^ 6 := by
      calc 729 = 3 ^ 6 := by norm_num
        _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    exact Nat.mul_pos (by omega) (by omega)
  calc 2 * (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)) = q ^ 6 * (q ^ 6 - 1) * (2 * (q ^ 2 - 1)) := by ring
    _ < q ^ 6 * (q ^ 6 - 1) * (q ^ 6 - 2) := Nat.mul_lt_mul_of_pos_left (by omega) hApos

theorem quad_bad_numbers {T : Type} [Group T] [Finite T] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hq : 3 ≤ p ^ e)
    (hcard : Nat.card T = (p ^ e) ^ 6 * ((p ^ e) ^ 6 - 1) * ((p ^ e) ^ 2 - 1)) :
    ∀ k : Kind, ¬ KindFactor k T := by
  refine bad_of_pow_dvd (ℓ := p) (a := 6 * e) hp hp2 (by omega) ?_ ?_
  · rw [hcard, ← pow_mul, mul_comm e 6]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _
  · have h6 : p ^ (6 * e) = (p ^ e) ^ 6 := by rw [← pow_mul, mul_comm e 6]
    rw [hcard, h6]
    exact quad_ineq hq

theorem ree_ineq {q : ℕ} (hq : 27 ≤ q) :
    2 * (q ^ 3 * (q - 1) * (q ^ 3 + 1)) < q ^ 3 * (q ^ 3 - 1) * (q ^ 3 - 2) := by
  have hx : 729 * q ≤ q ^ 3 := by
    calc 729 * q ≤ q ^ 2 * q := Nat.mul_le_mul_right q (by nlinarith)
      _ = q ^ 3 := by ring
  have hApos : 0 < q ^ 3 := by positivity
  calc 2 * (q ^ 3 * (q - 1) * (q ^ 3 + 1)) = q ^ 3 * (2 * ((q - 1) * (q ^ 3 + 1))) := by ring
    _ < q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 - 2)) := by
      apply Nat.mul_lt_mul_of_pos_left _ hApos
      obtain ⟨s, hs⟩ : ∃ s, q ^ 3 = 729 * q + s := ⟨q ^ 3 - 729 * q, by omega⟩
      obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
      rw [Nat.add_sub_cancel, hs]
      have e1 : 729 * (t + 1) + s - 1 = 729 * t + 728 + s := by omega
      have e2 : 729 * (t + 1) + s - 2 = 729 * t + 727 + s := by omega
      rw [e1, e2]
      nlinarith [Nat.zero_le s, Nat.zero_le t]
    _ = q ^ 3 * (q ^ 3 - 1) * (q ^ 3 - 2) := by ring

theorem ree_bad_numbers {T : Type} [Group T] [Finite T] {b : ℕ} (hb : 1 ≤ b)
    (hcard : Nat.card T = (3 ^ (2 * b + 1)) ^ 3 * (3 ^ (2 * b + 1) - 1) * ((3 ^ (2 * b + 1)) ^ 3 + 1)) :
    ∀ k : Kind, ¬ KindFactor k T := by
  refine bad_of_pow_dvd (ℓ := 3) (a := 3 * (2 * b + 1)) Nat.prime_three (by norm_num) (by omega) ?_ ?_
  · have h6 : 3 ^ (3 * (2 * b + 1)) = (3 ^ (2 * b + 1)) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [hcard, h6]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _
  · have h6 : 3 ^ (3 * (2 * b + 1)) = (3 ^ (2 * b + 1)) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [hcard, h6]
    have h27 : 27 ≤ 3 ^ (2 * b + 1) := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ree_ineq h27

theorem not_card_sl2_dvd_factorial_cube {c : ℕ} (hc : 3 ≤ c) :
    ¬ (c ^ 3 * ((c ^ 3) ^ 2 - 1)) ∣ Nat.factorial 11 := by
  intro h
  have h11 : Nat.factorial 11 = 39916800 := by decide
  have hle := Nat.le_of_dvd (Nat.factorial_pos 11) h
  rw [h11] at hle h
  by_cases h6 : 7 ≤ c
  · have h1 : 7 ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left h6 3
    have h2 : (7 ^ 3) ^ 2 ≤ (c ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (7 ^ 3) * ((7 ^ 3) ^ 2 - 1) ≤ c ^ 3 * ((c ^ 3) ^ 2 - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    norm_num at h3
    omega
  · interval_cases c <;> norm_num at h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
