module

public import CFSG.Open.Defs
import CFSG.GH74.Generic.S3.L3ClassC2T2

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupOutOrders

open CFSG.Open

theorem eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  have h : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
    obtain ⟨m, rfl⟩ := hq; omega
  have h1 : q ^ 2 % 8 = 1 := by
    rcases h with h | h | h | h <;> simp [Nat.pow_mod, h]
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by obtain ⟨m, rfl⟩ := hq; omega)
  omega

theorem sixteen_dvd_sub_one_mul {q : ℕ} (hq : Odd q) : 16 ∣ (q ^ 6 - 1) * (q ^ 2 - 1) := by
  have h8 := eight_dvd_sq_sub_one hq
  have h6 : q ^ 2 - 1 ∣ q ^ 6 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 3
    rwa [one_pow, ← pow_mul] at this
  exact (by norm_num : (16 : ℕ) ∣ 8 * 8).trans (Nat.mul_dvd_mul (h8.trans h6) h8)

theorem sixteen_dvd_ordG2 {q : ℕ} (hq : Odd q) : 16 ∣ ordG2 q := by
  unfold ordG2
  rw [mul_assoc]
  exact (sixteen_dvd_sub_one_mul hq).mul_left _

theorem sixteen_dvd_ordTrialityD4 {q : ℕ} (hq : Odd q) : 16 ∣ ordTrialityD4 q := by
  unfold ordTrialityD4
  rw [mul_assoc, mul_assoc]
  exact ((sixteen_dvd_sub_one_mul hq).mul_left _).mul_left _

theorem three_pow_odd_mod_sixteen (k : ℕ) :
    3 ^ (2 * k + 1) % 16 = 3 ∨ 3 ^ (2 * k + 1) % 16 = 11 := by
  induction k with
  | zero => left; norm_num
  | succ k ih =>
    have : 3 ^ (2 * (k + 1) + 1) = 9 * 3 ^ (2 * k + 1) := by ring
    omega

theorem ordRee_mod_sixteen {a : ℕ} (ha : a % 16 = 3 ∨ a % 16 = 11) :
    (a ^ 3 * (a ^ 3 + 1) * (a - 1)) % 16 = 8 := by
  rcases ha with ha | ha
  · have h1 : (a - 1) % 16 = 2 := by omega
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, ha, h1]
  · have h1 : (a - 1) % 16 = 10 := by omega
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, ha, h1]

theorem not_sixteen_dvd_ordRee (k : ℕ) : ¬ 16 ∣ ordRee (3 ^ (2 * k + 1)) := by
  intro hd
  have h := ordRee_mod_sixteen (three_pow_odd_mod_sixteen k)
  unfold ordRee at hd
  omega

theorem not_sixteen_dvd_J1 : ¬ 16 ∣ 175560 := by decide

theorem pow_dvd_bound {p m A B C : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hAB : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ A → ℓ ∣ B → ℓ = 2)
    (hBC : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ B → ℓ ∣ C → False)
    (hAC : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ A → ℓ ∣ C → ℓ = 3)
    (h9 : 3 ∣ A → 3 ∣ C → ¬ 9 ∣ C) (hd : p ^ m ∣ A ^ 2 * B * C) :
    p ^ m ≤ 3 * (A ^ 2 + B + C) := by
  have cop : ∀ n : ℕ, ¬ p ∣ n → Nat.Coprime (p ^ m) n := fun n hn =>
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  by_cases hpA : p ∣ A
  · have hpB : ¬ p ∣ B := fun h => hp2 (hAB p hp hpA h)
    have h1 : p ^ m ∣ A ^ 2 * C := by
      have : p ^ m ∣ (A ^ 2 * C) * B := by
        rwa [show A ^ 2 * C * B = A ^ 2 * B * C by ring]
      exact (cop B hpB).dvd_of_dvd_mul_right this
    by_cases hpC : p ∣ C
    · have hp3 : p = 3 := hAC p hp hpA hpC
      subst hp3
      have h9' := h9 hpA hpC
      obtain ⟨C', hC'⟩ := hpC
      have hC'3 : ¬ 3 ∣ C' := fun h => h9' (by
        rw [hC']; exact (mul_dvd_mul_left 3 h : 3 * 3 ∣ 3 * C'))
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp; omega
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h2 : 3 ^ m' ∣ A ^ 2 * C' := by
          rw [hC', pow_succ] at h1
          have : 3 ^ m' * 3 ∣ 3 * (A ^ 2 * C') := by
            rw [show 3 * (A ^ 2 * C') = A ^ 2 * (3 * C') by ring]; exact h1
          rw [mul_comm (3 ^ m') 3] at this
          exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
        have hcop : Nat.Coprime (3 ^ m') C' :=
          Nat.Coprime.pow_left m' ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC'3)
        have h3 : 3 ^ m' ∣ A ^ 2 := hcop.dvd_of_dvd_mul_right h2
        have h4 := Nat.le_of_dvd (by positivity) h3
        rw [pow_succ]
        nlinarith
    · have h2 : p ^ m ∣ A ^ 2 := (cop C hpC).dvd_of_dvd_mul_right h1
      have := Nat.le_of_dvd (by positivity) h2
      nlinarith
  · have hpA2 : ¬ p ∣ A ^ 2 := fun h => hpA (hp.dvd_of_dvd_pow h)
    have h1 : p ^ m ∣ B * C := by
      have : p ^ m ∣ A ^ 2 * (B * C) := by rwa [← mul_assoc]
      exact (cop _ hpA2).dvd_of_dvd_mul_left this
    by_cases hpB : p ∣ B
    · have hpC : ¬ p ∣ C := fun h => hBC p hp hpB h
      have h2 : p ^ m ∣ B := (cop C hpC).dvd_of_dvd_mul_right h1
      have := Nat.le_of_dvd hB h2
      nlinarith
    · have h2 : p ^ m ∣ C := (cop B hpB).dvd_of_dvd_mul_left h1
      have := Nat.le_of_dvd hC h2
      nlinarith

theorem dvd_bound_quad {p m x A B : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hA : 0 < A) (hB : 0 < B)
    (hAx : (A = x ∧ B = x + 2) ∨ (A = x + 3 ∧ B = x + 1))
    (hd : p ^ m ∣ A ^ 2 * B * (x ^ 2 + 3 * x + 3)) :
    p ^ m ≤ 3 * (A ^ 2 + B + (x ^ 2 + 3 * x + 3)) := by
  have hC : x ^ 2 + 3 * x + 3 = x * (x + 3) + 3 := by ring
  have hdA : ∀ ℓ : ℕ, ℓ ∣ A → ℓ ∣ x * (x + 3) := by
    intro ℓ h
    rcases hAx with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Dvd.dvd.mul_right h _
    · exact Dvd.dvd.mul_left h _
  refine pow_dvd_bound hp hp2 hA hB (by positivity) ?_ ?_ ?_ ?_ hd
  · intro ℓ hℓ h1 h2
    have : ℓ ∣ 2 := by
      rcases hAx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (Nat.dvd_add_right h1).1 h2
      · exact (Nat.dvd_add_right h2).1 h1
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this
  · intro ℓ hℓ h1 h2
    have h3 : ℓ ∣ 1 := by
      rcases hAx with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · have e : x ^ 2 + 3 * x + 3 = (x + 2) * (x + 1) + 1 := by ring
        rw [e] at h2
        exact (Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).1 h2
      · have e : x ^ 2 + 3 * x + 3 = (x + 1) * (x + 2) + 1 := by ring
        rw [e] at h2
        exact (Nat.dvd_add_right (Dvd.dvd.mul_right h1 _)).1 h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 h3)
  · intro ℓ hℓ h1 h2
    have h3 : ℓ ∣ x * (x + 3) + 3 := by rwa [← hC]
    have : ℓ ∣ 3 := (Nat.dvd_add_right (hdA ℓ h1)).1 h3
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this
  · intro h1 h2 h3
    have hx3 : 3 ∣ x := by
      rcases hAx with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact h1
      · exact (Nat.dvd_add_left (dvd_refl 3)).1 h1
    obtain ⟨b, rfl⟩ := hx3
    have : 9 ∣ 3 := by
      have e : (3 * b) ^ 2 + 3 * (3 * b) + 3 = 9 * (b ^ 2 + b) + 3 := by ring
      rw [e] at h3
      exact (Nat.dvd_add_right (dvd_mul_right 9 _)).1 h3
    omega

theorem dvd_bound_L3 {p m r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hd : p ^ m ∣ (r ^ 2 - 1) * (r ^ 3 - 1)) : p ^ m ≤ 9 * (r + 1) ^ 2 := by
  obtain ⟨x, rfl⟩ : ∃ x, r = x + 1 := ⟨r - 1, by omega⟩
  have hx : 0 < x := by omega
  have e2 : (x + 1) ^ 2 - 1 = x * (x + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (x + 1) ^ 3 - 1 = x * (x ^ 2 + 3 * x + 3) := Nat.sub_eq_of_eq_add (by ring)
  rw [e2, e3, show x * (x + 2) * (x * (x ^ 2 + 3 * x + 3)) =
    x ^ 2 * (x + 2) * (x ^ 2 + 3 * x + 3) by ring] at hd
  have := dvd_bound_quad (A := x) (B := x + 2) hp hp2 hx (by omega) (Or.inl ⟨rfl, rfl⟩) hd
  nlinarith

theorem dvd_bound_U3 {p m r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)
    (hd : p ^ m ∣ (r ^ 2 - 1) * (r ^ 3 + 1)) : p ^ m ≤ 9 * (r + 1) ^ 2 := by
  obtain ⟨x, rfl⟩ : ∃ x, r = x + 2 := ⟨r - 2, by omega⟩
  have e2 : (x + 2) ^ 2 - 1 = (x + 1) * (x + 3) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (x + 2) ^ 3 + 1 = (x + 3) * (x ^ 2 + 3 * x + 3) := by ring
  rw [e2, e3, show (x + 1) * (x + 3) * ((x + 3) * (x ^ 2 + 3 * x + 3)) =
    (x + 3) ^ 2 * (x + 1) * (x ^ 2 + 3 * x + 3) by ring] at hd
  have := dvd_bound_quad (A := x + 3) (B := x + 1) hp hp2 (by omega) (by omega)
    (Or.inr ⟨rfl, rfl⟩) hd
  nlinarith

theorem dvd_bound_of_dvd_r {p m r R : ℕ} (hp : p.Prime) (hr : 0 < r) (hR : ¬ p ∣ R)
    (hd : p ^ m ∣ r ^ 3 * R) : p ^ m ≤ r ^ 3 := by
  have hcop : Nat.Coprime (p ^ m) R :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 hR)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hd)

theorem not_dvd_sub_one {p r : ℕ} (hp : p.Prime) (hpr : p ∣ r) (hr : 0 < r) :
    ¬ p ∣ (r ^ 2 - 1) * (r ^ 3 - 1) := by
  intro h
  have h1 : p ∣ r ^ 2 - 1 ∨ p ∣ r ^ 3 - 1 := hp.dvd_mul.1 h
  have hp2 : p ∣ r ^ 2 := dvd_pow hpr (by norm_num)
  have hp3 : p ∣ r ^ 3 := dvd_pow hpr (by norm_num)
  have a2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  have a3 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ hr
  rcases h1 with h1 | h1
  · have := Nat.dvd_sub hp2 h1
    rw [Nat.sub_sub_self a2] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  · have := Nat.dvd_sub hp3 h1
    rw [Nat.sub_sub_self a3] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem not_dvd_add_one {p r : ℕ} (hp : p.Prime) (hpr : p ∣ r) (hr : 0 < r) :
    ¬ p ∣ (r ^ 2 - 1) * (r ^ 3 + 1) := by
  intro h
  have h1 : p ∣ r ^ 2 - 1 ∨ p ∣ r ^ 3 + 1 := hp.dvd_mul.1 h
  have hp2 : p ∣ r ^ 2 := dvd_pow hpr (by norm_num)
  have hp3 : p ∣ r ^ 3 := dvd_pow hpr (by norm_num)
  have a2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr
  rcases h1 with h1 | h1
  · have := Nat.dvd_sub hp2 h1
    rw [Nat.sub_sub_self a2] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  · have := (Nat.dvd_add_right hp3).1 h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)

open CFSG.GH74.Generic.S3 in
theorem shape3_bounds {p m N r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (hdvd : p ^ m ∣ N)
    (hN : N = ordA 2 r ∨ N = ordTwistedA 2 r) :
    (p ^ m ≤ r ^ 3 ∨ p ^ m ≤ 9 * (r + 1) ^ 2) ∧ r ^ 8 ≤ 12 * N := by
  have hr0 : 0 < r := by omega
  have b2 : r ^ 2 ≤ 2 * (r ^ 2 - 1) := by
    have : 4 ≤ r ^ 2 := by nlinarith
    omega
  have b3 : r ^ 3 ≤ 2 * (r ^ 3 - 1) := by
    have : 8 ≤ r ^ 3 := by nlinarith [Nat.pow_le_pow_left hr 3]
    omega
  have b5 : r ^ 5 ≤ 4 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
    have := Nat.mul_le_mul b2 b3
    calc r ^ 5 = r ^ 2 * r ^ 3 := by ring
      _ ≤ 2 * (r ^ 2 - 1) * (2 * (r ^ 3 - 1)) := this
      _ = 4 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by ring
  rcases hN with rfl | rfl
  · have h := L3Ord.ordA_two_mul r (by omega)
    have hg : Nat.gcd 3 (r - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hd : p ^ m ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) :=
      hdvd.trans ⟨Nat.gcd 3 (r - 1), by rw [← h]⟩
    refine ⟨?_, ?_⟩
    · by_cases hpr : p ∣ r
      · exact Or.inl (dvd_bound_of_dvd_r hp hr0 (not_dvd_sub_one hp hpr hr0) hd)
      · right
        have hcop : Nat.Coprime (p ^ m) (r ^ 3) :=
          Nat.Coprime.pow_left m (Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr))
        exact dvd_bound_L3 hp hp2 hr (hcop.dvd_of_dvd_mul_left hd)
    · calc r ^ 8 = r ^ 3 * r ^ 5 := by ring
        _ ≤ r ^ 3 * (4 * ((r ^ 2 - 1) * (r ^ 3 - 1))) := Nat.mul_le_mul_left _ b5
        _ = 4 * (r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1))) := by ring
        _ = 4 * (ordA 2 r * Nat.gcd 3 (r - 1)) := by rw [h]
        _ ≤ 4 * (ordA 2 r * 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hg)
        _ = 12 * ordA 2 r := by ring
  · have h := L3Ord.ordTwistedA_two_mul r
    have hg : Nat.gcd 3 (r + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have hd : p ^ m ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1)) :=
      hdvd.trans ⟨Nat.gcd 3 (r + 1), by rw [← h]⟩
    refine ⟨?_, ?_⟩
    · by_cases hpr : p ∣ r
      · exact Or.inl (dvd_bound_of_dvd_r hp hr0 (not_dvd_add_one hp hpr hr0) hd)
      · right
        have hcop : Nat.Coprime (p ^ m) (r ^ 3) :=
          Nat.Coprime.pow_left m (Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr))
        exact dvd_bound_U3 hp hp2 hr (hcop.dvd_of_dvd_mul_left hd)
    · have b5' : r ^ 5 ≤ 4 * ((r ^ 2 - 1) * (r ^ 3 + 1)) := by
        refine b5.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
      calc r ^ 8 = r ^ 3 * r ^ 5 := by ring
        _ ≤ r ^ 3 * (4 * ((r ^ 2 - 1) * (r ^ 3 + 1))) := Nat.mul_le_mul_left _ b5'
        _ = 4 * (r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1))) := by ring
        _ = 4 * (ordTwistedA 2 r * Nat.gcd 3 (r + 1)) := by rw [h]
        _ ≤ 4 * (ordTwistedA 2 r * 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hg)
        _ = 12 * ordTwistedA 2 r := by ring

theorem ordG2_le (q : ℕ) : ordG2 q ≤ q ^ 14 := by
  unfold ordG2
  calc q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≤ q ^ 6 * q ^ 6 * q ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.sub_le _ _)) (Nat.sub_le _ _)
    _ = q ^ 14 := by ring

theorem ordTrialityD4_le {q : ℕ} (hq : 2 ≤ q) : ordTrialityD4 q ≤ 2 * q ^ 28 := by
  unfold ordTrialityD4
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h44 : 2 ≤ q ^ 4 := by nlinarith [Nat.pow_le_pow_left hq 4]
  have h8 : q ^ 8 + q ^ 4 + 1 ≤ 2 * q ^ 8 := by
    have : q ^ 8 = q ^ 4 * q ^ 4 := by ring
    nlinarith
  calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * (2 * q ^ 8) * q ^ 6 * q ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl h8) (Nat.sub_le _ _)) (Nat.sub_le _ _)
    _ = 2 * q ^ 28 := by ring

theorem g2_not_shape3 {p e r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hr : 3 ≤ r)
    (hN : ordG2 (p ^ e) = ordA 2 r ∨ ordG2 (p ^ e) = ordTwistedA 2 r) : False := by
  have hdvd : p ^ (6 * e) ∣ ordG2 (p ^ e) := by
    unfold ordG2
    rw [mul_comm 6 e, pow_mul]
    exact ((dvd_refl _).mul_right _).mul_right _
  obtain ⟨h1, h2⟩ := shape3_bounds hp hp2 (by omega) hdvd hN
  have hup := ordG2_le (p ^ e)
  rw [mul_comm 6 e, pow_mul] at h1
  generalize p ^ e = q at *
  have hq0 : 0 < q ^ 14 := by positivity
  rcases h1 with h1 | h1
  · have hqr : q ^ 2 ≤ r := by
      by_contra hlt
      have := Nat.pow_lt_pow_left (not_le.1 hlt) (by norm_num : 3 ≠ 0)
      have e : (q ^ 2) ^ 3 = q ^ 6 := by ring
      omega
    have h16 : (q ^ 2) ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hqr 8
    have h25 : 25 * q ^ 14 ≤ q ^ 2 * q ^ 14 :=
      Nat.mul_le_mul_right _ (by nlinarith [Nat.pow_le_pow_left hq 2])
    have e16 : (q ^ 2) ^ 8 = q ^ 2 * q ^ 14 := by ring
    omega
  · have h18 : q ^ 6 ≤ 18 * r ^ 2 := by nlinarith
    have h24 : (q ^ 6) ^ 4 ≤ (18 * r ^ 2) ^ 4 := Nat.pow_le_pow_left h18 4
    have e24 : (q ^ 6) ^ 4 = q ^ 14 * q ^ 10 := by ring
    have e8 : (18 * r ^ 2) ^ 4 = 104976 * r ^ 8 := by ring
    have h10 : 9765625 * q ^ 14 ≤ q ^ 14 * q ^ 10 := by
      have := Nat.mul_le_mul_left (q ^ 14) (Nat.pow_le_pow_left hq 10)
      linarith
    omega

theorem d4_not_shape3 {p e r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 3 ≤ p ^ e) (hr : 3 ≤ r)
    (hN : ordTrialityD4 (p ^ e) = ordA 2 r ∨ ordTrialityD4 (p ^ e) = ordTwistedA 2 r) : False := by
  have hdvd : p ^ (12 * e) ∣ ordTrialityD4 (p ^ e) := by
    unfold ordTrialityD4
    rw [mul_comm 12 e, pow_mul]
    exact (((dvd_refl _).mul_right _).mul_right _).mul_right _
  obtain ⟨h1, h2⟩ := shape3_bounds hp hp2 (by omega) hdvd hN
  have hup := ordTrialityD4_le (q := p ^ e) (by omega)
  rw [mul_comm 12 e, pow_mul] at h1
  generalize p ^ e = q at *
  have hq0 : 0 < q ^ 28 := by positivity
  rcases h1 with h1 | h1
  · have hqr : q ^ 4 ≤ r := by
      by_contra hlt
      have := Nat.pow_lt_pow_left (not_le.1 hlt) (by norm_num : 3 ≠ 0)
      have e : (q ^ 4) ^ 3 = q ^ 12 := by ring
      omega
    have h32 : (q ^ 4) ^ 8 ≤ r ^ 8 := Nat.pow_le_pow_left hqr 8
    have h81 : 81 * q ^ 28 ≤ q ^ 4 * q ^ 28 :=
      Nat.mul_le_mul_right _ (by nlinarith [Nat.pow_le_pow_left hq 4])
    have e32 : (q ^ 4) ^ 8 = q ^ 4 * q ^ 28 := by ring
    omega
  · have h18 : q ^ 12 ≤ 18 * r ^ 2 := by nlinarith
    have h48 : (q ^ 12) ^ 4 ≤ (18 * r ^ 2) ^ 4 := Nat.pow_le_pow_left h18 4
    have e48 : (q ^ 12) ^ 4 = q ^ 28 * q ^ 20 := by ring
    have e8 : (18 * r ^ 2) ^ 4 = 104976 * r ^ 8 := by ring
    have h20 : 3486784401 * q ^ 28 ≤ q ^ 28 * q ^ 20 := by
      have := Nat.mul_le_mul_left (q ^ 28) (Nat.pow_le_pow_left hq 20)
      linarith
    omega

end CFSG.GH74.Generic.BProg.B2.PumpupOutOrders
