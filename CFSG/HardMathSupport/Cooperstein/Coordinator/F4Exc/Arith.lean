module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Family

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint.Chevalley

theorem exists_gh {n g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) : ∃ gh : ℕ, 2 ^ n - 1 = (2 ^ g - 1) * gh := by
  obtain ⟨t, rfl⟩ := hgn
  have hdvd : 2 ^ g - 1 ∣ 2 ^ (g * t) - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ g) 1 t
    rwa [one_pow, ← pow_mul] at this
  exact hdvd

theorem gh_odd {n g gh : ℕ} (hn : 1 ≤ n) (hgh : 2 ^ n - 1 = (2 ^ g - 1) * gh) : Odd gh := by
  have h1 : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); rw [pow_succ]; omega⟩
  rw [hgh] at h1
  exact (Nat.odd_mul.1 h1).2

theorem two_pow_le_gh {n g gh : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (ht2 : 2 ≤ n / g)
    (hgh : 2 ^ n - 1 = (2 ^ g - 1) * gh) : 2 ^ (n - g) ≤ gh := by
  obtain ⟨t, rfl⟩ := hgn
  have ht : g * t / g = t := Nat.mul_div_cancel_left t (by omega)
  rw [ht] at ht2
  by_contra hlt
  push Not at hlt
  have h1 : gh ≤ 2 ^ (g * t - g) - 1 := by omega
  have h2 : (2 ^ g - 1) * gh ≤ (2 ^ g - 1) * (2 ^ (g * t - g) - 1) := Nat.mul_le_mul_left _ h1
  have hpos : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hpos2 : 1 ≤ 2 ^ (g * t - g) := Nat.one_le_two_pow
  have e : 2 ^ (g * t) = 2 ^ g * 2 ^ (g * t - g) := by
    rw [← pow_add]; congr 1; have : g ≤ g * t := Nat.le_mul_of_pos_right _ (by omega); omega
  have hg2 : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hgt2 : 2 * g ≤ g * t := by nlinarith
  have hg3 : 2 ≤ 2 ^ (g * t - g) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (g * t - g) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hgh.symm] at h2
  obtain ⟨X, hX⟩ : ∃ X, 2 ^ g = X + 1 := ⟨2 ^ g - 1, by omega⟩
  obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ (g * t - g) = Y + 1 := ⟨2 ^ (g * t - g) - 1, by omega⟩
  rw [e, hX, hY] at h2
  rw [hX] at hg2
  rw [hY] at hg3
  simp only [Nat.add_sub_cancel] at h2
  have : (X + 1) * (Y + 1) - 1 ≤ X * Y := h2
  have h3 : (X + 1) * (Y + 1) = X * Y + X + Y + 1 := by ring
  omega

theorem three_le_gh {n g gh : ℕ} (hn : 1 ≤ n) (hg : 1 ≤ g) (hgn : g ∣ n) (ht2 : 2 ≤ n / g)
    (hgh : 2 ^ n - 1 = (2 ^ g - 1) * gh) : 3 ≤ gh := by
  have hodd := gh_odd hn hgh
  have h1 := two_pow_le_gh hg hgn ht2 hgh
  have h2 : 2 ≤ 2 ^ (n - g) := by
    obtain ⟨t, rfl⟩ := hgn
    have ht : g * t / g = t := Nat.mul_div_cancel_left t (by omega)
    rw [ht] at ht2
    have hgt2 : 2 * g ≤ g * t := by nlinarith
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (g * t - g) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨m, hm⟩ := hodd
  omega

theorem not_dvd_pow_sub_one {n g gh j : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (ht2 : 2 ≤ n / g)
    (hgh : 2 ^ n - 1 = (2 ^ g - 1) * gh) (hj0 : 0 < j) (hjn : j < n) : ¬ gh ∣ 2 ^ j - 1 := by
  intro hd
  have hd1 : gh ∣ 2 ^ n - 1 := ⟨2 ^ g - 1, by rw [hgh]; ring⟩
  have hd2 : gh ∣ Nat.gcd (2 ^ n - 1) (2 ^ j - 1) := Nat.dvd_gcd hd1 hd
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hd2
  set e := Nat.gcd n j with he
  have hepos : 0 < e := Nat.gcd_pos_of_pos_right _ hj0
  have hen : e ∣ n := Nat.gcd_dvd_left n j
  have hej : e ≤ j := Nat.le_of_dvd hj0 (Nat.gcd_dvd_right n j)
  have hlt : e < n := by omega
  have h2e : 2 * e ≤ n := by
    obtain ⟨q, hq⟩ := hen
    have : 2 ≤ q := by
      by_contra h
      have : q ≤ 1 := by omega
      interval_cases q
      · omega
      · omega
    nlinarith
  have h2g : 2 * g ≤ n := by
    obtain ⟨t, rfl⟩ := hgn
    have ht : g * t / g = t := Nat.mul_div_cancel_left t (by omega)
    rw [ht] at ht2
    nlinarith
  have h2e' : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hepos
  have hle : gh ≤ 2 ^ e - 1 := Nat.le_of_dvd (by omega) hd2
  have h1 := two_pow_le_gh hg hgn ht2 hgh
  have : 2 ^ (n - g) < 2 ^ e := by
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 this
  omega

theorem odd_coprime_two_pow {g : ℕ} (hg : Odd g) (b : ℕ) : IsCoprime (g : ℤ) ((2 : ℤ) ^ b) := by
  refine IsCoprime.pow_right ?_
  obtain ⟨k, rfl⟩ := hg
  exact ⟨1, -(k : ℤ), by push_cast; ring⟩

theorem sep_gamma {n gh : ℕ} (hgh3 : 3 ≤ gh) (hodd : Odd gh)
    (hord : ∀ j, 0 < j → j < n → ¬ gh ∣ 2 ^ j - 1)
    {ι : Type*} (γ : ι → Fin Tag.F4.rank → ℤ)
    (hcont : ∀ i, ∀ d m : ℕ, (∀ c, (d : ℤ) ∣ (m : ℤ) * γ i c) → d ∣ m)
    (hmin : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c c', (d : ℤ) ∣ minorF (γ i) (γ i') c c')
    {i i' : ι} {b b' : ℕ} (hb : b < n) (hb' : b' < n)
    (h : ∀ c, (gh : ℤ) ∣ (2 : ℤ) ^ b * γ i c - (2 : ℤ) ^ b' * γ i' c) : i = i' ∧ b = b' := by
  have hcop := odd_coprime_two_pow hodd
  by_cases hii : i = i'
  · subst hii
    refine ⟨rfl, ?_⟩
    by_contra hbb
    have key : ∀ b b' : ℕ, b < b' → b' < n → (∀ c, (gh : ℤ) ∣ (2 : ℤ) ^ b * γ i c - (2 : ℤ) ^ b' * γ i c) →
        False := by
      intro b b' hlt hb' h
      have h1 : ∀ c, (gh : ℤ) ∣ (((2 ^ b' - 2 ^ b : ℕ)) : ℤ) * γ i c := by
        intro c
        have := (dvd_neg).2 (h c)
        have e : (((2 ^ b' - 2 ^ b : ℕ)) : ℤ) = (2 : ℤ) ^ b' - 2 ^ b := by
          rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) hlt.le)]; push_cast; ring
        rw [e]
        convert this using 1
        ring
      have h2 := hcont i gh _ h1
      have e2 : 2 ^ b' - 2 ^ b = 2 ^ b * (2 ^ (b' - b) - 1) := by
        have : 2 ^ b' = 2 ^ b * 2 ^ (b' - b) := by
          rw [← pow_add]; congr 1; omega
        rw [this, Nat.mul_sub, Nat.mul_one]
      rw [e2] at h2
      have h3 : gh ∣ 2 ^ (b' - b) - 1 := by
        have hc : Nat.Coprime gh (2 ^ b) := Nat.Coprime.pow_right _ (hodd.coprime_two_right)
        exact hc.dvd_of_dvd_mul_left h2
      exact hord (b' - b) (by omega) (by omega) h3
    rcases Nat.lt_or_gt_of_ne hbb with hlt | hgt
    · exact key b b' hlt hb' h
    · refine key b' b hgt hb fun c => ?_
      have := (dvd_neg).2 (h c)
      convert this using 1
      ring
  · exfalso
    apply hmin i i' hii gh hgh3
    intro c c'
    have h1 := h c
    have h2 := h c'
    have e : (2 : ℤ) ^ b * minorF (γ i) (γ i') c c' =
        (2 ^ b * γ i c - 2 ^ b' * γ i' c) * γ i' c' - (2 ^ b * γ i c' - 2 ^ b' * γ i' c') * γ i' c := by
      unfold minorF; ring
    have h3 : (gh : ℤ) ∣ (2 : ℤ) ^ b * minorF (γ i) (γ i') c c' := by
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)
    exact (hcop b).dvd_of_dvd_mul_left h3

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
