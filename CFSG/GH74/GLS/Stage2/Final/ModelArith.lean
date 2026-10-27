module

public import CFSG.Open.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelArith

open CFSG.Open

theorem two_mul_ordBC_two {q : ℕ} (hq : Odd q) :
    2 * ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have h2 : Nat.gcd 2 (q - 1) = 2 :=
    Nat.gcd_eq_left (by rcases hq with ⟨k, rfl⟩; exact ⟨k, by omega⟩)
  have hp : (∏ i ∈ Finset.Icc 1 2, (q ^ (2 * i) - 1)) = (q ^ 2 - 1) * (q ^ 4 - 1) := by
    have e : Finset.Icc 1 2 = {1, 2} := by decide
    rw [e]; simp
  have hdvd : 2 ∣ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    have h : Even (q ^ 2 - 1) := Nat.Odd.sub_odd (hq.pow) odd_one
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h.two_dvd _) _
  unfold ordBC
  rw [h2, hp]
  exact Nat.mul_div_cancel' hdvd

theorem gcd_mul_ordA_three {q : ℕ} :
    Nat.gcd 4 (q - 1) * ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
  have hp : (∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1)) =
      (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by
    have e : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
    rw [e]; simp [mul_assoc]
  have hdvd : Nat.gcd (3 + 1) (q - 1) ∣
      q ^ (3 * (3 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
    have h1 : Nat.gcd (3 + 1) (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 3 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow q 1 3
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left (h1.trans h2) _) _) _
  unfold ordA
  rw [hp]
  have := Nat.mul_div_cancel' hdvd
  norm_num at this ⊢
  exact this

theorem gcd_mul_ordTwistedA_three {q : ℕ} :
    Nat.gcd 4 (q + 1) * ordTwistedA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
  have hp : (∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - (-1 : ℤ) ^ i).toNat) =
      (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) := by
    have e : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
    rw [e]
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self,
      not_false_eq_true, Finset.prod_insert, Finset.prod_singleton, show (3:ℕ) ≠ 4 by decide,
      show (2:ℕ) ≠ 3 by decide, show (2:ℕ) ≠ 4 by decide]
    have h2 : ((q:ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
      have : ((q:ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 : ℕ) : ℤ) - 1 := by push_cast; ring
      rw [this]; omega
    have h3 : ((q:ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
      have : ((q:ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this]; exact Int.toNat_natCast _
    have h4 : ((q:ℤ) ^ 4 - (-1) ^ 4).toNat = q ^ 4 - 1 := by
      have : ((q:ℤ) ^ 4 - (-1) ^ 4) = ((q ^ 4 : ℕ) : ℤ) - 1 := by push_cast; ring
      rw [this]; omega
    rw [h2, h3, h4, mul_assoc]
  have hdvd : Nat.gcd (3 + 1) (q + 1) ∣
      q ^ (3 * (3 + 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
    have h1 : Nat.gcd (3 + 1) (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
    have h2 : q + 1 ∣ q ^ 2 - 1 := by
      refine ⟨q - 1, ?_⟩
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have : (k + 1) ^ 2 - 1 = (k + 1 + 1) * k := by
          have : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
          omega
        rw [this]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right (h1.trans h2) _) _) _
  unfold ordTwistedA
  rw [hp]
  have := Nat.mul_div_cancel' hdvd
  norm_num at this ⊢
  exact this

theorem not_dvd_pow_sub_one {ℓ q m : ℕ} (hℓ : ℓ.Prime) (hq : ℓ ∣ q) (hq0 : 0 < q) (hm : m ≠ 0) :
    ¬ ℓ ∣ q ^ m - 1 := by
  intro h
  have h1 : ℓ ∣ q ^ m := dvd_pow hq hm
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq0
  have h2 : ℓ ∣ 1 := by
    have := (Nat.dvd_sub h1 h)
    simpa [Nat.sub_sub_self hpos] using this
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)

theorem not_dvd_pow_add_one {ℓ q m : ℕ} (hℓ : ℓ.Prime) (hq : ℓ ∣ q) (hm : m ≠ 0) :
    ¬ ℓ ∣ q ^ m + 1 := by
  intro h
  have h1 : ℓ ∣ q ^ m := dvd_pow hq hm
  have h2 : ℓ ∣ 1 := (Nat.dvd_add_right h1).1 h
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)

theorem not_dvd_two {ℓ : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) : ¬ ℓ ∣ 2 := by
  intro h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)

theorem not_dvd_of_dvd_four {ℓ d : ℕ} (hℓ : ℓ.Prime) (h2 : ℓ ≠ 2) (hd : d ∣ 4) : ¬ ℓ ∣ d := by
  intro h
  have h4 : ℓ ∣ 4 := h.trans hd
  have : ℓ ∣ 2 ^ 2 := by simpa using h4
  exact not_dvd_two hℓ h2 (hℓ.dvd_of_dvd_pow this)

theorem three_le_pow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) : 3 ≤ p ^ f := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  calc 3 ≤ p := h3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem prime_pow_dvd_mul3 {ℓ k a b c : ℕ} (hℓ : ℓ.Prime) (hab : ¬ (ℓ ∣ a ∧ ℓ ∣ b))
    (hac : ¬ (ℓ ∣ a ∧ ℓ ∣ c)) (hbc : ¬ (ℓ ∣ b ∧ ℓ ∣ c)) (h : ℓ ^ k ∣ a * b * c) :
    ℓ ^ k ∣ a ∨ ℓ ^ k ∣ b ∨ ℓ ^ k ∣ c := by
  have cop : ∀ x : ℕ, ¬ ℓ ∣ x → Nat.Coprime (ℓ ^ k) x := fun x hx =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hx)
  by_cases ha : ℓ ∣ a
  · have hb : ¬ ℓ ∣ b := fun hb => hab ⟨ha, hb⟩
    have hc : ¬ ℓ ∣ c := fun hc => hac ⟨ha, hc⟩
    left
    exact (cop b hb).dvd_of_dvd_mul_right ((cop c hc).dvd_of_dvd_mul_right h)
  · by_cases hb : ℓ ∣ b
    · have hc : ¬ ℓ ∣ c := fun hc => hbc ⟨hb, hc⟩
      right; left
      exact (cop a ha).dvd_of_dvd_mul_left ((cop c hc).dvd_of_dvd_mul_right h)
    · right; right
      rw [mul_assoc] at h
      exact (cop b hb).dvd_of_dvd_mul_left ((cop a ha).dvd_of_dvd_mul_left h)

theorem sq_pow_le_of_dvd {ℓ q m : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hq : 3 ≤ q)
    (h : ℓ ^ (2 * m) ∣ (q ^ 2 - 1) * (q ^ 4 - 1)) : ℓ ^ m ≤ q + 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 2 ≤ r := by omega
  have e : ((r + 1) ^ 2 - 1) * ((r + 1) ^ 4 - 1) = r ^ 2 * (r + 2) ^ 2 * ((r + 1) ^ 2 + 1) := by
    have e1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : (r + 1) ^ 4 - 1 = r * (r + 2) * ((r + 1) ^ 2 + 1) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2]; ring
  rw [e] at h
  have h2 := not_dvd_two hℓ hℓ2
  have key : ℓ ^ (2 * m) ∣ r ^ 2 ∨ ℓ ^ (2 * m) ∣ (r + 2) ^ 2 ∨
      ℓ ^ (2 * m) ∣ (r + 1) ^ 2 + 1 := by
    refine prime_pow_dvd_mul3 hℓ ?_ ?_ ?_ h
    · rintro ⟨ha, hb⟩
      have ha' := hℓ.dvd_of_dvd_pow ha
      have hb' := hℓ.dvd_of_dvd_pow hb
      exact h2 ((Nat.dvd_add_right ha').1 hb')
    · rintro ⟨ha, hc⟩
      have ha' := hℓ.dvd_of_dvd_pow ha
      have : (r + 1) ^ 2 + 1 = r * (r + 2) + 2 := by ring
      rw [this] at hc
      exact h2 ((Nat.dvd_add_right (Dvd.dvd.mul_right ha' _)).1 hc)
    · rintro ⟨hb, hc⟩
      have hb' := hℓ.dvd_of_dvd_pow hb
      have : (r + 1) ^ 2 + 1 = (r + 2) * r + 2 := by ring
      rw [this] at hc
      exact h2 ((Nat.dvd_add_right (Dvd.dvd.mul_right hb' _)).1 hc)
  have hsq : (ℓ ^ m) ^ 2 = ℓ ^ (2 * m) := by rw [← pow_mul, mul_comm]
  rcases key with k | k | k
  · have := Nat.le_of_dvd (by positivity) k
    rw [← hsq] at this
    have : ℓ ^ m ≤ r := by nlinarith
    omega
  · have := Nat.le_of_dvd (by positivity) k
    rw [← hsq] at this
    have : ℓ ^ m ≤ r + 2 := by nlinarith
    omega
  · have := Nat.le_of_dvd (by positivity) k
    rw [← hsq] at this
    have : ℓ ^ m ≤ r + 1 := by nlinarith
    omega

theorem size_ineq {q : ℕ} (hq : 3 ≤ q) :
    2 * (q + 1) ^ 5 ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 3 := ⟨q - 3, by omega⟩
  have h1 : r + 3 ≤ (r + 3) ^ 2 - 1 := by
    have : r + 3 + 1 ≤ (r + 3) ^ 2 := by nlinarith
    omega
  have h2 : (r + 3) ^ 3 ≤ (r + 3) ^ 4 - 1 := by
    have : (r + 3) ^ 3 + 1 ≤ (r + 3) ^ 4 := by nlinarith [pow_pos (show 0 < r + 3 by omega) 3]
    omega
  have h3 : 2 * (r + 3 + 1) ^ 5 ≤ (r + 3) ^ 8 := by
    have : (r + 3) ^ 8 = 2 * (r + 3 + 1) ^ 5 + (r ^ 8 + 24 * r ^ 7 + 252 * r ^ 6 + 1510 * r ^ 5 +
        5630 * r ^ 4 + 13288 * r ^ 3 + 19132 * r ^ 2 + 14936 * r + 4513) := by ring
    omega
  calc 2 * (r + 3 + 1) ^ 5 ≤ (r + 3) ^ 8 := h3
    _ = (r + 3) ^ 4 * ((r + 3) * (r + 3) ^ 3) := by ring
    _ ≤ (r + 3) ^ 4 * (((r + 3) ^ 2 - 1) * ((r + 3) ^ 4 - 1)) := by gcongr

theorem Y_lt_L {a : ℕ} (ha : 1 ≤ a) : (a ^ 2 - 1) * (a ^ 3 - 1) * (a ^ 4 - 1) < 2 * a ^ 9 := by
  have h2 : a ^ 2 - 1 ≤ a ^ 2 := Nat.sub_le _ _
  have h3 : a ^ 3 - 1 ≤ a ^ 3 := Nat.sub_le _ _
  have h4 : a ^ 4 - 1 ≤ a ^ 4 := Nat.sub_le _ _
  have hpos : 0 < a ^ 9 := by positivity
  calc (a ^ 2 - 1) * (a ^ 3 - 1) * (a ^ 4 - 1) ≤ a ^ 2 * a ^ 3 * a ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4
    _ = a ^ 9 := by ring
    _ < 2 * a ^ 9 := by omega

theorem Y_lt_U {a : ℕ} (ha : 1 ≤ a) : (a ^ 2 - 1) * (a ^ 3 + 1) * (a ^ 4 - 1) < 2 * a ^ 9 := by
  have h2 : a ^ 2 - 1 < a ^ 2 := Nat.sub_lt (by positivity) one_pos
  have h4 : a ^ 4 - 1 ≤ a ^ 4 := Nat.sub_le _ _
  have h3 : a ^ 3 + 1 ≤ 2 * a ^ 3 := by
    have : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ ha
    omega
  have hpos : 0 < a ^ 4 := by positivity
  calc (a ^ 2 - 1) * (a ^ 3 + 1) * (a ^ 4 - 1) ≤ (a ^ 2 - 1) * (2 * a ^ 3) * a ^ 4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h4
    _ < a ^ 2 * (2 * a ^ 3) * a ^ 4 := by
        apply Nat.mul_lt_mul_of_pos_right _ hpos
        exact Nat.mul_lt_mul_of_pos_right h2 (by positivity)
    _ = 2 * a ^ 9 := by ring

theorem not_eq_diff_prime {p p' f f' N d Y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp' : p'.Prime)
    (hp'2 : p' ≠ 2) (hf : 1 ≤ f) (hf' : 1 ≤ f') (hne : p ≠ p') (hd4 : d ∣ 4) (hd2 : 2 ≤ d)
    (H1 : 2 * N = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)))
    (H2 : d * N = (p' ^ f') ^ 6 * Y) (hY : Y < 2 * (p' ^ f') ^ 9) : False := by
  have hq3 : 3 ≤ p ^ f := three_le_pow hp hp2 hf
  have hq'3 : 3 ≤ p' ^ f' := three_le_pow hp' hp'2 hf'
  set q := p ^ f with hqdef
  set q' := p' ^ f' with hq'def
  have hp'q : ¬ p' ∣ q := by
    intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq hp' hp).1 (hp'.dvd_of_dvd_pow h)).symm
  have hcop : Nat.Coprime (q' ^ 6) (d * q ^ 4) := by
    have h1 : Nat.Coprime p' (d * q ^ 4) := by
      refine Nat.Coprime.mul_right
        ((Nat.Prime.coprime_iff_not_dvd hp').2 (not_dvd_of_dvd_four hp' hp'2 hd4)) ?_
      exact Nat.Coprime.pow_right 4 ((Nat.Prime.coprime_iff_not_dvd hp').2 hp'q)
    have := Nat.Coprime.pow (f' * 6) 1 h1
    simpa [hq'def, ← pow_mul, mul_comm] using this
  have hdvd : q' ^ 6 ∣ (d * q ^ 4) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    have : (d * q ^ 4) * ((q ^ 2 - 1) * (q ^ 4 - 1)) = 2 * (q' ^ 6 * Y) := by
      calc (d * q ^ 4) * ((q ^ 2 - 1) * (q ^ 4 - 1))
          = d * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by ring
        _ = d * (2 * N) := by rw [H1]
        _ = 2 * (d * N) := by ring
        _ = 2 * (q' ^ 6 * Y) := by rw [H2]
    rw [this]
    exact Dvd.dvd.mul_left (Dvd.intro Y rfl) 2
  have hW : q' ^ 6 ∣ (q ^ 2 - 1) * (q ^ 4 - 1) := hcop.dvd_of_dvd_mul_left hdvd
  have hW' : p' ^ (2 * (3 * f')) ∣ (q ^ 2 - 1) * (q ^ 4 - 1) := by
    have : q' ^ 6 = p' ^ (2 * (3 * f')) := by
      rw [hq'def, ← pow_mul]; congr 1; ring
    rwa [this] at hW
  have hle : p' ^ (3 * f') ≤ q + 1 := sq_pow_le_of_dvd hp' hp'2 hq3 hW'
  have hq'3le : q' ^ 3 ≤ q + 1 := by
    have : q' ^ 3 = p' ^ (3 * f') := by rw [hq'def, ← pow_mul]; congr 1; ring
    rwa [this]
  have h5 : (q' ^ 3) ^ 5 ≤ (q + 1) ^ 5 := Nat.pow_le_pow_left hq'3le 5
  have h6 : d * N < 2 * (q + 1) ^ 5 := by
    calc d * N = q' ^ 6 * Y := H2
      _ < q' ^ 6 * (2 * q' ^ 9) := by
        apply Nat.mul_lt_mul_of_pos_left hY (by positivity)
      _ = 2 * (q' ^ 3) ^ 5 := by ring
      _ ≤ 2 * (q + 1) ^ 5 := by omega
  have h7 := size_ineq hq3
  have h8 : 2 * N ≤ d * N := Nat.mul_le_mul_right N hd2
  omega

theorem same_prime_core {p f f' d Y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hf' : 1 ≤ f')
    (hd4 : d ∣ 4) (hY : ¬ p ∣ Y)
    (hmain : d * ((p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1))) =
      2 * ((p ^ f') ^ 6 * Y)) :
    (p ^ f') ^ 3 = (p ^ f) ^ 2 ∧
      d * (((p ^ f') ^ 3 - 1) * ((p ^ f') ^ 6 - 1)) = 2 * Y := by
  have hq3 : 3 ≤ p ^ f := three_le_pow hp hp2 hf
  have hq'3 : 3 ≤ p ^ f' := three_le_pow hp hp2 hf'
  set q := p ^ f with hqdef
  set q' := p ^ f' with hq'def
  have hpq : p ∣ q := dvd_pow_self p (by omega)
  have hnd2 := not_dvd_two hp hp2
  have hndd := not_dvd_of_dvd_four hp hp2 hd4
  have hW : ¬ p ∣ (q ^ 2 - 1) * (q ^ 4 - 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact not_dvd_pow_sub_one hp hpq (by omega) (by norm_num) h
    · exact not_dvd_pow_sub_one hp hpq (by omega) (by norm_num) h
  have hcop1 : Nat.Coprime (q ^ 4) (2 * Y) := by
    have : Nat.Coprime p (2 * Y) :=
      Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd2)
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hY)
    exact Nat.Coprime.pow_left 4 (by simpa [hqdef] using Nat.Coprime.pow_left f this)
  have hcop2 : Nat.Coprime (q' ^ 6) (d * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by
    have : Nat.Coprime p (d * ((q ^ 2 - 1) * (q ^ 4 - 1))) :=
      Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hndd)
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hW)
    exact Nat.Coprime.pow_left 6 (by simpa [hq'def] using Nat.Coprime.pow_left f' this)
  have hd1 : q ^ 4 ∣ q' ^ 6 := by
    have h1 : q ^ 4 ∣ (2 * Y) * q' ^ 6 := by
      have : q ^ 4 ∣ d * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) :=
        Dvd.dvd.mul_left (Dvd.intro _ rfl) d
      rw [hmain] at this
      have e : 2 * (q' ^ 6 * Y) = (2 * Y) * q' ^ 6 := by ring
      rwa [e] at this
    exact hcop1.dvd_of_dvd_mul_left h1
  have hd2 : q' ^ 6 ∣ q ^ 4 := by
    have h1 : q' ^ 6 ∣ (d * ((q ^ 2 - 1) * (q ^ 4 - 1))) * q ^ 4 := by
      have : q' ^ 6 ∣ 2 * (q' ^ 6 * Y) := Dvd.dvd.mul_left (Dvd.intro _ rfl) 2
      rw [← hmain] at this
      have e : d * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) =
          (d * ((q ^ 2 - 1) * (q ^ 4 - 1))) * q ^ 4 := by ring
      rwa [e] at this
    exact hcop2.dvd_of_dvd_mul_left h1
  have hq4 : q ^ 4 = q' ^ 6 := Nat.dvd_antisymm hd1 hd2
  have hq2 : q' ^ 3 = q ^ 2 := by
    have h : (q ^ 2) ^ 2 = (q' ^ 3) ^ 2 := by
      calc (q ^ 2) ^ 2 = q ^ 4 := by ring
        _ = q' ^ 6 := hq4
        _ = (q' ^ 3) ^ 2 := by ring
    exact ((Nat.pow_left_injective (by norm_num : 2 ≠ 0)) h).symm
  refine ⟨hq2, ?_⟩
  have hqpos : 0 < q' ^ 6 := by positivity
  apply Nat.eq_of_mul_eq_mul_left hqpos
  have e1 : q ^ 2 - 1 = q' ^ 3 - 1 := by rw [hq2]
  have e2 : q ^ 4 - 1 = q' ^ 6 - 1 := by rw [hq4]
  rw [e1, e2, hq4] at hmain
  calc q' ^ 6 * (d * ((q' ^ 3 - 1) * (q' ^ 6 - 1)))
      = d * (q' ^ 6 * ((q' ^ 3 - 1) * (q' ^ 6 - 1))) := by ring
    _ = 2 * (q' ^ 6 * Y) := hmain
    _ = q' ^ 6 * (2 * Y) := by ring

theorem final_L {d a : ℕ} (hd2 : 2 ≤ d) (ha : 3 ≤ a)
    (h : d * (a ^ 6 - 1) = 2 * ((a ^ 2 - 1) * (a ^ 4 - 1))) : False := by
  have h1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h' : (d : ℤ) * ((a : ℤ) ^ 6 - 1) = 2 * (((a : ℤ) ^ 2 - 1) * ((a : ℤ) ^ 4 - 1)) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3] at this
    linarith
  have hd2' : (2 : ℤ) ≤ d := by exact_mod_cast hd2
  have ha' : (3 : ℤ) ≤ a := by exact_mod_cast ha
  have h6 : (0 : ℤ) ≤ (a : ℤ) ^ 6 - 1 := by
    nlinarith [pow_pos (show (0:ℤ) < a by linarith) 6,
      one_le_pow₀ (show (1:ℤ) ≤ a by linarith) (n := 6)]
  nlinarith [mul_le_mul_of_nonneg_right hd2' h6, sq_nonneg ((a:ℤ)^2),
    pow_pos (show (0:ℤ) < a by linarith) 2, pow_pos (show (0:ℤ) < a by linarith) 4]

theorem final_U {d a : ℕ} (hd4 : d ∣ 4) (hd2 : 2 ≤ d) (ha : 3 ≤ a)
    (h : d * (a ^ 3 - 1) ^ 2 = 2 * ((a ^ 2 - 1) * (a ^ 4 - 1))) : False := by
  have h1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h' : (d : ℤ) * ((a : ℤ) ^ 3 - 1) ^ 2 = 2 * (((a : ℤ) ^ 2 - 1) * ((a : ℤ) ^ 4 - 1)) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3] at this
    linarith
  have hd : d = 2 ∨ d = 4 := by
    have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
    interval_cases d
    · left; rfl
    · exact absurd hd4 (by norm_num)
    · right; rfl
  have ha' : (3 : ℤ) ≤ a := by exact_mod_cast ha
  have hapos : (0 : ℤ) < a := by linarith
  rcases hd with rfl | rfl
  · have key : 2 * ((a : ℤ) ^ 3 - 1) ^ 2 - 2 * (((a : ℤ) ^ 2 - 1) * ((a : ℤ) ^ 4 - 1)) =
        2 * ((a : ℤ) ^ 2 * ((a : ℤ) - 1) ^ 2) := by ring
    have hpos : (0 : ℤ) < (a : ℤ) ^ 2 * ((a : ℤ) - 1) ^ 2 := by
      apply mul_pos (by positivity)
      have : (0 : ℤ) < (a : ℤ) - 1 := by linarith
      positivity
    push_cast at h'
    linarith
  · push_cast at h'
    nlinarith [pow_pos hapos 2, pow_pos hapos 3, pow_pos hapos 4, pow_pos hapos 6,
      mul_pos (pow_pos hapos 3) (pow_pos hapos 3)]

theorem sq_sub_one_eq (a : ℕ) (ha : 1 ≤ a) : a ^ 2 - 1 = (a - 1) * (a + 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have : (b + 1) ^ 2 - 1 = b * (b + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [this]; simp

theorem not_eq_L {p p' f f' N d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp' : p'.Prime)
    (hp'2 : p' ≠ 2) (hf : 1 ≤ f) (hf' : 1 ≤ f') (hd4 : d ∣ 4) (hd2 : 2 ≤ d)
    (H1 : 2 * N = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)))
    (H2 : d * N = (p' ^ f') ^ 6 *
      (((p' ^ f') ^ 2 - 1) * ((p' ^ f') ^ 3 - 1) * ((p' ^ f') ^ 4 - 1))) : False := by
  by_cases hpp : p = p'
  · subst hpp
    have hq'3 : 3 ≤ p ^ f' := three_le_pow hp hp2 hf'
    have hpq' : p ∣ p ^ f' := dvd_pow_self p (by omega)
    have hY : ¬ p ∣ ((p ^ f') ^ 2 - 1) * ((p ^ f') ^ 3 - 1) * ((p ^ f') ^ 4 - 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact not_dvd_pow_sub_one hp hpq' (by omega) (by norm_num) h
        · exact not_dvd_pow_sub_one hp hpq' (by omega) (by norm_num) h
      · exact not_dvd_pow_sub_one hp hpq' (by omega) (by norm_num) h
    have hmain : d * ((p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1))) =
        2 * ((p ^ f') ^ 6 * (((p ^ f') ^ 2 - 1) * ((p ^ f') ^ 3 - 1) * ((p ^ f') ^ 4 - 1))) := by
      rw [← H1, ← H2]; ring
    obtain ⟨-, h⟩ := same_prime_core hp hp2 hf hf' hd4 hY hmain
    set q' := p ^ f' with hq'
    have hpos : 0 < q' ^ 3 - 1 := by
      have : 8 ≤ q' ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ q' ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    apply final_L hd2 hq'3 (a := q')
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc (q' ^ 3 - 1) * (d * (q' ^ 6 - 1)) = d * ((q' ^ 3 - 1) * (q' ^ 6 - 1)) := by ring
      _ = 2 * ((q' ^ 2 - 1) * (q' ^ 3 - 1) * (q' ^ 4 - 1)) := h
      _ = (q' ^ 3 - 1) * (2 * ((q' ^ 2 - 1) * (q' ^ 4 - 1))) := by ring
  · refine not_eq_diff_prime hp hp2 hp' hp'2 hf hf' hpp hd4 hd2 H1 H2 (Y_lt_L ?_)
    have := three_le_pow hp' hp'2 hf'
    omega

theorem not_eq_U {p p' f f' N d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp' : p'.Prime)
    (hp'2 : p' ≠ 2) (hf : 1 ≤ f) (hf' : 1 ≤ f') (hd4 : d ∣ 4) (hd2 : 2 ≤ d)
    (H1 : 2 * N = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)))
    (H2 : d * N = (p' ^ f') ^ 6 *
      (((p' ^ f') ^ 2 - 1) * ((p' ^ f') ^ 3 + 1) * ((p' ^ f') ^ 4 - 1))) : False := by
  by_cases hpp : p = p'
  · subst hpp
    have hq'3 : 3 ≤ p ^ f' := three_le_pow hp hp2 hf'
    have hpq' : p ∣ p ^ f' := dvd_pow_self p (by omega)
    have hY : ¬ p ∣ ((p ^ f') ^ 2 - 1) * ((p ^ f') ^ 3 + 1) * ((p ^ f') ^ 4 - 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact not_dvd_pow_sub_one hp hpq' (by omega) (by norm_num) h
        · exact not_dvd_pow_add_one hp hpq' (by norm_num) h
      · exact not_dvd_pow_sub_one hp hpq' (by omega) (by norm_num) h
    have hmain : d * ((p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1))) =
        2 * ((p ^ f') ^ 6 * (((p ^ f') ^ 2 - 1) * ((p ^ f') ^ 3 + 1) * ((p ^ f') ^ 4 - 1))) := by
      rw [← H1, ← H2]; ring
    obtain ⟨-, h⟩ := same_prime_core hp hp2 hf hf' hd4 hY hmain
    set q' := p ^ f' with hq'
    have hpos : 0 < q' ^ 3 + 1 := by positivity
    apply final_U hd4 hd2 hq'3 (a := q')
    apply Nat.eq_of_mul_eq_mul_left hpos
    have e : q' ^ 6 - 1 = (q' ^ 3 - 1) * (q' ^ 3 + 1) := by
      have h1 : 1 ≤ q' ^ 3 := Nat.one_le_pow _ _ (by omega)
      have := sq_sub_one_eq (q' ^ 3) h1
      rw [← pow_mul] at this
      simpa using this
    calc (q' ^ 3 + 1) * (d * (q' ^ 3 - 1) ^ 2)
        = d * ((q' ^ 3 - 1) * ((q' ^ 3 - 1) * (q' ^ 3 + 1))) := by ring
      _ = d * ((q' ^ 3 - 1) * (q' ^ 6 - 1)) := by rw [e]
      _ = 2 * ((q' ^ 2 - 1) * (q' ^ 3 + 1) * (q' ^ 4 - 1)) := h
      _ = (q' ^ 3 + 1) * (2 * ((q' ^ 2 - 1) * (q' ^ 4 - 1))) := by ring
  · refine not_eq_diff_prime hp hp2 hp' hp'2 hf hf' hpp hd4 hd2 H1 H2 (Y_lt_U ?_)
    have := three_le_pow hp' hp'2 hf'
    omega

theorem lt_of_orders_L {N M d e q : ℕ} (hq : 2 ≤ q) (hd : d ≤ 4) (he : 1 ≤ e)
    (h1 : e * N = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)))
    (h2 : d * M = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1))) : N < M := by
  have hA : N ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    calc N = 1 * N := (one_mul N).symm
      _ ≤ e * N := Nat.mul_le_mul_right N he
      _ = _ := h1
  have h3 : 7 ≤ q ^ 3 - 1 := by
    have : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have h4 : q ^ 2 ≤ q ^ 2 - 1 + 1 := by omega
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hApos : 0 < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    have : 1 ≤ q ^ 2 - 1 := by omega
    have : 1 ≤ q ^ 4 - 1 := by
      have : 16 ≤ q ^ 4 := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    positivity
  have h5 : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) =
      (q ^ 2 * (q ^ 3 - 1)) * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by ring
  have h6 : 28 ≤ q ^ 2 * (q ^ 3 - 1) := by nlinarith
  by_contra hNM
  have hNM : M ≤ N := not_lt.1 hNM
  have : d * M ≤ 4 * M := Nat.mul_le_mul_right M hd
  have h7 : 4 * M ≤ 4 * N := by omega
  rw [h5] at h2
  nlinarith

theorem lt_of_orders_U {N M d e q : ℕ} (hq : 2 ≤ q) (hd : d ≤ 4) (he : 1 ≤ e)
    (h1 : e * N = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)))
    (h2 : d * M = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))) : N < M := by
  have hA : N ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    calc N = 1 * N := (one_mul N).symm
      _ ≤ e * N := Nat.mul_le_mul_right N he
      _ = _ := h1
  have h3 : 9 ≤ q ^ 3 + 1 := by
    have : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hApos : 0 < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    have : 1 ≤ q ^ 2 - 1 := by omega
    have : 1 ≤ q ^ 4 - 1 := by
      have : 16 ≤ q ^ 4 := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    positivity
  have h5 : q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) =
      (q ^ 2 * (q ^ 3 + 1)) * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by ring
  have h6 : 36 ≤ q ^ 2 * (q ^ 3 + 1) := by nlinarith
  by_contra hNM
  have hNM : M ≤ N := not_lt.1 hNM
  have : d * M ≤ 4 * M := Nat.mul_le_mul_right M hd
  have h7 : 4 * M ≤ 4 * N := by omega
  rw [h5] at h2
  nlinarith

end CFSG.GH74.GLS.Stage2.Final.ModelArith
