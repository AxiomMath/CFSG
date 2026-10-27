module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2OutH

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG.ClassicalInvolution.Asc77.T7F2

variable {G : Type} [Group G] {R : Subgroup G} {x y : G} {n : ℕ}

private theorem tp_x_pow_ne_one (c : QuatCoord R x y n) : x ^ (2 ^ n) ≠ 1 := by
  intro h
  have h' : x ^ ((2 ^ n : ℕ) : ℤ) = x ^ (0 : ℤ) := by
    rw [zpow_natCast, zpow_zero]
    exact h
  have hd : (2 : ℤ) ^ (n + 1) ∣ ((2 ^ n : ℕ) : ℤ) - 0 := c.zpow_eq_iff.mp h'
  rw [sub_zero] at hd
  have hle : (2 : ℤ) ^ (n + 1) ≤ ((2 ^ n : ℕ) : ℤ) := Int.le_of_dvd (by positivity) hd
  push_cast at hle
  have hpos : (0 : ℤ) < 2 ^ n := by positivity
  have e : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  linarith

private theorem tp_conj_y {m : G} {i j : ℤ} (hx : m * x * m⁻¹ = x ^ i)
    (hy : m * y * m⁻¹ = y * x ^ j) (k : ℤ) :
    m * (y * x ^ k) * m⁻¹ = y * x ^ (j + i * k) := by
  have hxk : m * x ^ k * m⁻¹ = x ^ (i * k) := by
    rw [← conj_zpow, hx, ← zpow_mul]
  calc m * (y * x ^ k) * m⁻¹ = (m * y * m⁻¹) * (m * x ^ k * m⁻¹) := by group
    _ = (y * x ^ j) * x ^ (i * k) := by rw [hy, hxk]
    _ = y * x ^ (j + i * k) := by rw [mul_assoc, ← zpow_add]

private theorem tp_no_comm (c : QuatCoord R x y n) {m w : G}
    (hno : ¬ ∃ w ∈ R, orderOf w = 4 ∧ w * m = m * w) (hwR : w ∈ R)
    (hw2 : w * w = x ^ (2 ^ n)) (hc : m * w * m⁻¹ = w) : False := by
  refine hno ⟨w, hwR, ?_, (mul_inv_eq_iff_eq_mul.mp hc).symm⟩
  have hsq : w ^ 2 ≠ 1 := by
    rw [pow_two, hw2]
    exact tp_x_pow_ne_one c
  have hfour : w ^ (2 ^ (1 + 1)) = 1 := by
    have e4 : w ^ (2 ^ (1 + 1)) = x ^ (2 ^ (n + 1)) := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two, hw2, ← pow_add]
      congr 1
      ring
    rw [e4, c.pow_card]
  have h4 := orderOf_eq_prime_pow (p := 2) (n := 1) hsq hfour
  norm_num at h4
  exact h4

theorem involution_cond (c : QuatCoord R x y n) {m : G} {i j : ℤ} (hm : m * m = 1)
    (hx : m * x * m⁻¹ = x ^ i) (hy : m * y * m⁻¹ = y * x ^ j) :
    (2 : ℤ) ^ (n + 1) ∣ i * i - 1 ∧ (2 : ℤ) ^ (n + 1) ∣ j * (i + 1) := by
  have ha := Out.coord_mul_a hx hx
  have hb := Out.coord_mul_b hx hy hy
  rw [hm, inv_one, one_mul, mul_one] at ha hb
  have hA : x ^ (1 : ℤ) = x ^ (i * i) := by
    rw [zpow_one]
    exact ha
  have hB : y * x ^ (0 : ℤ) = y * x ^ (j + i * j) := by
    rw [zpow_zero, mul_one]
    exact hb
  refine ⟨dvd_sub_comm.mp (c.zpow_eq_iff.mp hA), ?_⟩
  have hC := c.zpow_eq_iff.mp (mul_left_cancel hB).symm
  rw [sub_zero] at hC
  have e : j * (i + 1) = j + i * j := by ring
  rw [e]
  exact hC

theorem sd_coord (c : QuatCoord R x y n) (hn : 2 ≤ n) {m : G} {i j : ℤ} (hm : m * m = 1)
    (hx : m * x * m⁻¹ = x ^ i) (hy : m * y * m⁻¹ = y * x ^ j)
    (hno : ¬ ∃ w ∈ R, orderOf w = 4 ∧ w * m = m * w) :
    (2 : ℤ) ^ (n + 1) ∣ i + 1 ∧ Odd j := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  obtain ⟨h1, h2⟩ := involution_cond c hm hx hy
  have hodd : Odd i := by
    rcases Int.even_or_odd i with ⟨t, ht⟩ | h
    · exfalso
      have h3 : (2 : ℤ) ∣ i * i - 1 := dvd_trans (dvd_pow_self (2 : ℤ) (by omega)) h1
      have e : i * i = 2 * (2 * (t * t)) := by
        rw [ht]
        ring
      omega
    · exact h
  have hnot4 : ¬ (4 : ℤ) ∣ i - 1 := by
    intro hdiv
    have hsq : x ^ (2 ^ (p + 1)) * x ^ (2 ^ (p + 1)) = x ^ (2 ^ (p + 2)) := by
      rw [← pow_add]
      congr 1
      ring
    have hcomm : m * x ^ (2 ^ (p + 1)) * m⁻¹ = x ^ (2 ^ (p + 1)) := by
      rw [← conj_pow, hx, ← zpow_natCast (x ^ i), ← zpow_mul, ← zpow_natCast x]
      refine c.zpow_eq_iff.mpr ?_
      have e : i * ((2 ^ (p + 1) : ℕ) : ℤ) - ((2 ^ (p + 1) : ℕ) : ℤ)
          = (i - 1) * ((2 ^ (p + 1) : ℕ) : ℤ) := by ring
      have e' : (2 : ℤ) ^ (p + 2 + 1) = 4 * ((2 ^ (p + 1) : ℕ) : ℤ) := by
        push_cast
        ring
      rw [e, e']
      exact mul_dvd_mul_right hdiv _
    exact tp_no_comm c hno (R.pow_mem c.ha (2 ^ (p + 1))) hsq hcomm
  obtain ⟨s, hs⟩ := hodd
  obtain ⟨t, ht⟩ : ∃ t : ℤ, i = 4 * t + 3 := ⟨(i - 3) / 4, by omega⟩
  have hPi : (2 : ℤ) ^ (p + 2) ∣ i + 1 := by
    have e : i * i - 1 = 2 * ((2 * t + 1) * (i + 1)) := by
      rw [ht]
      ring
    have h3 : (2 : ℤ) * 2 ^ (p + 2) ∣ 2 * ((2 * t + 1) * (i + 1)) := by
      have e2 : (2 : ℤ) * 2 ^ (p + 2) = 2 ^ (p + 2 + 1) := by ring
      rw [e2, ← e]
      exact h1
    have h4 : (2 : ℤ) ^ (p + 2) ∣ (2 * t + 1) * (i + 1) :=
      (mul_dvd_mul_iff_left (two_ne_zero : (2 : ℤ) ≠ 0)).mp h3
    have hcop : IsCoprime ((2 : ℤ) ^ (p + 2)) (2 * t + 1) :=
      ((Int.isCoprime_two_right.mpr (odd_two_mul_add_one t)).pow_right).symm
    exact hcop.dvd_of_dvd_mul_left h4
  obtain ⟨e, he⟩ := hPi
  have heven : Even e := by
    rcases Int.even_or_odd e with he0 | hoe
    · exact he0
    · exfalso
      have h7 : (2 : ℤ) ∣ j * e := by
        have h5 : (2 : ℤ) ^ (p + 2) * 2 ∣ (2 : ℤ) ^ (p + 2) * (j * e) := by
          have e1 : (2 : ℤ) ^ (p + 2) * 2 = 2 ^ (p + 2 + 1) := by ring
          have e2 : (2 : ℤ) ^ (p + 2) * (j * e) = j * (i + 1) := by
            rw [he]
            ring
          rw [e1, e2]
          exact h2
        exact (mul_dvd_mul_iff_left (pow_ne_zero _ (two_ne_zero : (2 : ℤ) ≠ 0))).mp h5
      rcases Int.prime_two.dvd_or_dvd h7 with h8 | h8
      · obtain ⟨j0, rfl⟩ := h8
        have hc0 : Odd (1 - (2 : ℤ) ^ (p + 1) * e) := ⟨-((2 : ℤ) ^ p * e), by ring⟩
        have hcop : IsCoprime (1 - (2 : ℤ) ^ (p + 1) * e) ((2 : ℤ) ^ (p + 2)) :=
          (Int.isCoprime_two_right.mpr hc0).pow_right
        obtain ⟨u, v, huv⟩ := hcop
        have hc : m * (y * x ^ (u * j0)) * m⁻¹ = y * x ^ (u * j0) := by
          rw [tp_conj_y hx hy (u * j0)]
          congr 1
          exact c.zpow_eq_iff.mpr ⟨v * j0, by linear_combination (u * j0) * he - (2 * j0) * huv⟩
        exact tp_no_comm c hno (R.mul_mem c.hb (R.zpow_mem c.ha (u * j0))) (c.sq_mul (u * j0)) hc
      · obtain ⟨r, hr⟩ := hoe
        omega
  obtain ⟨e', he'⟩ := heven
  have hdiv : (2 : ℤ) ^ (p + 2 + 1) ∣ i + 1 := ⟨e', by rw [he, he']; ring⟩
  refine ⟨hdiv, ?_⟩
  rcases Int.even_or_odd j with hje | hjo
  · exfalso
    obtain ⟨jh, hjh⟩ := hje
    obtain ⟨f, hf⟩ := hdiv
    have hc : m * (y * x ^ jh) * m⁻¹ = y * x ^ jh := by
      rw [tp_conj_y hx hy jh]
      congr 1
      exact c.zpow_eq_iff.mpr ⟨f * jh, by linear_combination hjh + jh * hf⟩
    exact tp_no_comm c hno (R.mul_mem c.hb (R.zpow_mem c.ha jh)) (c.sq_mul jh) hc
  · exact hjo

theorem ff_not_commute (c : QuatCoord R x y n) (hn : 2 ≤ n) {m₁ m₂ : G} {i₁ j₁ i₂ j₂ : ℤ}
    (hx₁ : m₁ * x * m₁⁻¹ = x ^ i₁) (hy₁ : m₁ * y * m₁⁻¹ = y * x ^ j₁)
    (hx₂ : m₂ * x * m₂⁻¹ = x ^ i₂) (hy₂ : m₂ * y * m₂⁻¹ = y * x ^ j₂)
    (hf₁ : (2 : ℤ) ^ (n + 1) ∣ i₁ - (1 + 2 ^ n)) (hf₁' : (2 : ℤ) ^ n ∣ j₁)
    (hsd₂ : (2 : ℤ) ^ (n + 1) ∣ i₂ + 1) (hsd₂' : Odd j₂) : m₁ * m₂ ≠ m₂ * m₁ := by
  intro h
  have key : (m₁ * m₂) * y * (m₁ * m₂)⁻¹ = (m₂ * m₁) * y * (m₂ * m₁)⁻¹ := by rw [h]
  rw [Out.coord_mul_b hx₁ hy₁ hy₂, Out.coord_mul_b hx₂ hy₂ hy₁] at key
  have h1 : x ^ (j₁ + i₁ * j₂) = x ^ (j₂ + i₂ * j₁) := mul_left_cancel key
  obtain ⟨e, he⟩ := c.zpow_eq_iff.mp h1
  obtain ⟨a, ha⟩ := hf₁
  obtain ⟨b, hb⟩ := hsd₂
  obtain ⟨k, hk⟩ := hsd₂'
  obtain ⟨j', hj'⟩ := hf₁'
  have hi₁ : i₁ = 1 + 2 ^ n + 2 ^ (n + 1) * a := by linarith
  have hi₂ : i₂ = -1 + 2 ^ (n + 1) * b := by linarith
  subst hi₁ hi₂ hj' hk
  have hfin : (2 : ℤ) ^ n * ((2 * k + 1) - 2 * (e - j' - a * (2 * k + 1) + 2 ^ n * b * j')) = 0 := by
    linear_combination he
  rcases mul_eq_zero.mp hfin with h0 | h0
  · have : (0 : ℤ) < 2 ^ n := by positivity
    linarith
  · have h9 : 2 * k + 1 = 2 * (e - j' - a * (2 * k + 1) + 2 ^ n * b * j') := by
      linear_combination h0
    obtain ⟨M, hM⟩ : ∃ M, 2 * k + 1 = 2 * M := ⟨_, h9⟩
    omega

theorem mult_of_mem_R (c : QuatCoord R x y n) {g : G} (hg : g ∈ R) :
    ∃ i : ℤ, (i = 1 ∨ i = -1) ∧ g * x * g⁻¹ = x ^ i := by
  rcases c.cover g hg with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [zpow_one]
    group
  · refine ⟨-1, Or.inr rfl, ?_⟩
    calc y * x ^ k * x * (y * x ^ k)⁻¹ = y * x * y⁻¹ := by group
      _ = x ^ (-1 : ℤ) := by rw [c.hbab, zpow_neg_one]

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
