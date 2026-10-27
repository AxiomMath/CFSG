module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2UniqDiv

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof

private theorem cl24_two_mul_N {τ : StatedLieTag} {n n' j d : ℕ}
    (hj : 0 < j) (hd : 0 < d) (hn' : 0 < n')
    (hN : lieSylowExponent τ n * j = lieSylowExponent .PSL n' * d)
    (hE : j * cl24E τ n = d * cl24E .PSL n') :
    2 * lieSylowExponent τ n = (n' - 1) * cl24E τ n := by
  have hcross := cl24_cross_NE hj hd hN hE
  have hE' : cl24E .PSL n' = n' := rfl
  have hN' : lieSylowExponent .PSL n' = n' * (n' - 1) / 2 := rfl
  rw [hE', hN'] at hcross
  have htri : 2 * (n' * (n' - 1) / 2) = n' * (n' - 1) := cl24_tri n'
  have key : (2 * lieSylowExponent τ n) * n' = ((n' - 1) * cl24E τ n) * n' := by
    calc (2 * lieSylowExponent τ n) * n'
        = 2 * (lieSylowExponent τ n * n') := by ring
      _ = 2 * ((n' * (n' - 1) / 2) * cl24E τ n) := by rw [hcross]
      _ = (2 * (n' * (n' - 1) / 2)) * cl24E τ n := by ring
      _ = (n' * (n' - 1)) * cl24E τ n := by rw [htri]
      _ = ((n' - 1) * cl24E τ n) * n' := by ring
  exact Nat.mul_right_cancel hn' key

theorem cl24_finPSL_cla {τ : StatedLieTag} {n n' j d : ℕ}
    (hτ : τ = .PSL ∨ τ = .PSU ∨ τ = .PSp ∨ τ = .POmegaOdd ∨ τ = .POmegaPlus ∨ τ = .POmegaMinus)
    (hadm : StatedLieAdmissible τ n 3 j) (hadm' : StatedLieAdmissible .PSL n' 3 d) (hjd : j < d)
    (hN : lieSylowExponent τ n * j = lieSylowExponent .PSL n' * d)
    (hE : j * cl24E τ n = d * cl24E .PSL n')
    (hX : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      s * (lieOrderDivisor .PSL n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ) ≠ 0 ∧
      (3 : ℤ) ^ (2 * j) ∣
        s * (lieOrderDivisor .PSL n' (3 ^ d) : ℤ) - s' * (lieOrderDivisor τ n (3 ^ j) : ℤ)) :
    False := by
  have hj : 0 < j := by have := hadm.2.1; omega
  have hd : 0 < d := by have := hadm'.2.1; omega
  have hn' : 0 < n' := by have := hadm'.2.2.1; omega
  have hsize := cl24_size_of_digit hX
  have h2N := cl24_two_mul_N hj hd hn' hN hE
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hn2 : 2 ≤ n := hadm.2.2.1
    have h1 : n * (n - 1) = (n' - 1) * n := by
      rw [← cl24_tri n]
      simpa only [lieSylowExponent, cl24E] using h2N
    have h2 : n * (n - 1) = n * (n' - 1) := by rw [h1]; ring
    have hnm1 : n - 1 = n' - 1 := Nat.mul_left_cancel (by omega : 0 < n) h2
    have hnn' : n' = n := by omega
    subst n'
    have hNpos : 0 < lieSylowExponent .PSL n := by
      simp only [lieSylowExponent]
      apply Nat.div_pos
      · simpa using Nat.mul_le_mul hn2 (by omega : 1 ≤ n - 1)
      · norm_num
    have : j = d := Nat.mul_left_cancel hNpos hN
    omega
  ·
    have hn3 : 3 ≤ n := hadm.2.2.1
    by_cases hEven : Even n
    ·
      have hx : cl24E .PSU n = 2 * (n - 1) := by
        simp only [cl24E]; exact if_pos hEven
      rw [hx] at h2N hE
      simp only [lieSylowExponent] at h2N
      simp only [cl24E] at hE
      have h1 : n * (n - 1) = (n' - 1) * (2 * (n - 1)) := by
        rw [← cl24_tri n]; exact h2N
      have h2 : n * (n - 1) = (2 * (n' - 1)) * (n - 1) := by rw [h1]; ring
      have hn_eq : n = 2 * (n' - 1) := Nat.mul_right_cancel (by omega : 0 < n - 1) h2
      have hn1 : n - 1 = 2 * n' - 3 := by omega
      rw [hn1] at hE
      have hval : j * (4 * n' - 6) = d * n' := by
        rw [← hE]; congr 1; omega
      have h1' : j * (4 * n') - j * 6 = d * n' := by
        rw [← Nat.mul_sub_left_distrib]; exact hval
      have hsum : 4 * j * n' = d * n' + 6 * j := by
        have hle : j * 6 ≤ j * (4 * n') := Nat.mul_le_mul_left j (by omega : 6 ≤ 4 * n')
        have h := Nat.sub_add_cancel hle
        rw [h1'] at h
        calc 4 * j * n' = j * (4 * n') := by ring
          _ = d * n' + j * 6 := h.symm
          _ = d * n' + 6 * j := by ring
      have hdle : d * n' ≤ 4 * j * n' := by rw [hsum]; exact Nat.le_add_right _ _
      have hd_le : d ≤ 4 * j := Nat.le_of_mul_le_mul_right hdle hn'
      have hsum' : 4 * j * n' - d * n' = 6 * j := by
        rw [hsum]; exact Nat.add_sub_cancel_left _ _
      have hkey : n' * (4 * j - d) = 6 * j := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_comm n' (4 * j), Nat.mul_comm n' d, ← hsum']
      have h4jd : 1 ≤ 4 * j - d := by
        by_contra h
        simp only [not_le] at h
        have : d = 4 * j := by omega
        rw [this] at hsum
        omega
      have hn'6 : n' ≤ 6 * j := by
        calc n' = n' * 1 := by ring
          _ ≤ n' * (4 * j - d) := Nat.mul_le_mul_left n' h4jd
          _ = 6 * j := hkey
      by_cases hj2 : 2 ≤ j
      · have hD : lieOrderDivisor .PSU n (3 ^ j) ≤ 3 ^ j + 1 := by
          simp only [lieOrderDivisor]
          exact Nat.gcd_le_right n (by positivity)
        have hD' : lieOrderDivisor .PSL n' (3 ^ d) ≤ 6 * j :=
          le_trans (Nat.le_of_dvd hn' (cl24_D_PSL_dvd n' (3 ^ d))) hn'6
        exact (not_le_of_gt (cl24_digit_contra6 hj2 hD hD')) hsize
      · have hj1 : j = 1 := by omega
        subst j
        have hd23 : d = 2 ∨ d = 3 := by omega
        rcases hd23 with rfl | rfl
        · have hk : n' * 2 = 6 := by simpa using hkey
          have hn'3 : n' = 3 := by omega
          subst hn'3
          have hn4 : n = 4 := by omega
          subst hn4
          simp only [lieOrderDivisor] at hsize
          norm_num at hsize
        · have hk : n' * 1 = 6 := by simpa using hkey
          have hn'6' : n' = 6 := by omega
          subst hn'6'
          have hn10 : n = 10 := by omega
          subst hn10
          simp only [lieOrderDivisor] at hsize
          norm_num at hsize
    ·
      have hx : cl24E .PSU n = 2 * n := by
        simp only [cl24E]; exact if_neg hEven
      rw [hx] at h2N hE
      simp only [lieSylowExponent] at h2N
      simp only [cl24E] at hE
      have h1 : n * (n - 1) = (n' - 1) * (2 * n) := by
        rw [← cl24_tri n]; exact h2N
      have h2 : n * (n - 1) = n * (2 * (n' - 1)) := by rw [h1]; ring
      have hn_eq : n - 1 = 2 * (n' - 1) := Nat.mul_left_cancel (by omega : 0 < n) h2
      have hn2 : n = 2 * n' - 1 := by omega
      rw [hn2] at hE
      have hval : j * (4 * n' - 2) = d * n' := by
        rw [← hE]; congr 1; omega
      have h1' : j * (4 * n') - j * 2 = d * n' := by
        rw [← Nat.mul_sub_left_distrib]; exact hval
      have hsum : 4 * j * n' = d * n' + 2 * j := by
        have hle : j * 2 ≤ j * (4 * n') := Nat.mul_le_mul_left j (by omega : 2 ≤ 4 * n')
        have h := Nat.sub_add_cancel hle
        rw [h1'] at h
        calc 4 * j * n' = j * (4 * n') := by ring
          _ = d * n' + j * 2 := h.symm
          _ = d * n' + 2 * j := by ring
      have hdle : d * n' ≤ 4 * j * n' := by rw [hsum]; exact Nat.le_add_right _ _
      have hd_le : d ≤ 4 * j := Nat.le_of_mul_le_mul_right hdle hn'
      have hsum' : 4 * j * n' - d * n' = 2 * j := by
        rw [hsum]; exact Nat.add_sub_cancel_left _ _
      have hkey : n' * (4 * j - d) = 2 * j := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_comm n' (4 * j), Nat.mul_comm n' d, ← hsum']
      have h4jd : 1 ≤ 4 * j - d := by
        by_contra h
        simp only [not_le] at h
        have : d = 4 * j := by omega
        rw [this] at hsum
        omega
      have hn'4 : n' ≤ 4 * j := by
        calc n' = n' * 1 := by ring
          _ ≤ n' * (4 * j - d) := Nat.mul_le_mul_left n' h4jd
          _ = 2 * j := hkey
          _ ≤ 4 * j := by omega
      have hD : lieOrderDivisor .PSU n (3 ^ j) ≤ 3 ^ j + 1 := by
        simp only [lieOrderDivisor]
        exact Nat.gcd_le_right n (by positivity)
      have hD' : lieOrderDivisor .PSL n' (3 ^ d) ≤ 4 * j :=
        le_trans (Nat.le_of_dvd hn' (cl24_D_PSL_dvd n' (3 ^ d))) hn'4
      exact (not_le_of_gt (cl24_digit_contra4 (by omega) hD hD')) hsize
  ·
    have hn2 : 2 ≤ n := hadm.2.2.1
    simp only [lieSylowExponent, cl24E] at h2N hE
    have h2N' : (2 * n) * n = (2 * n) * (n' - 1) := by
      calc (2 * n) * n = 2 * n ^ 2 := by ring
        _ = (n' - 1) * (2 * n) := h2N
        _ = (2 * n) * (n' - 1) := by ring
    have hn_eq : n = n' - 1 := Nat.mul_left_cancel (by omega : 0 < 2 * n) h2N'
    have hn'succ : n' = n + 1 := by omega
    rw [hn'succ] at hE
    have hdvd : n + 1 ∣ 2 * j * n := ⟨d, by rw [mul_comm (n + 1) d, ← hE]; ring⟩
    have hcop : Nat.Coprime (n + 1) n := by
      rw [Nat.coprime_comm]
      exact (Nat.coprime_self_add_right).mpr (by simp)
    have hdvd2 : n + 1 ∣ 2 * j := hcop.dvd_of_dvd_mul_right hdvd
    have hn'4 : n' ≤ 4 * j := by
      have : n + 1 ≤ 2 * j := Nat.le_of_dvd (by omega : 0 < 2 * j) hdvd2
      omega
    have hD : lieOrderDivisor .PSp n (3 ^ j) ≤ 3 ^ j + 1 := by
      simp only [lieOrderDivisor]
      have hg : Nat.gcd 2 (3 ^ j - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
      have h3 : 3 ≤ 3 ^ j := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
    have hD' : lieOrderDivisor .PSL n' (3 ^ d) ≤ 4 * j :=
      le_trans (Nat.le_of_dvd hn' (cl24_D_PSL_dvd n' (3 ^ d))) hn'4
    exact (not_le_of_gt (cl24_digit_contra4 (by omega) hD hD')) hsize
  ·
    have hn3 : 3 ≤ n := hadm.2.2.1
    simp only [lieSylowExponent, cl24E] at h2N hE
    have h2N' : (2 * n) * n = (2 * n) * (n' - 1) := by
      calc (2 * n) * n = 2 * n ^ 2 := by ring
        _ = (n' - 1) * (2 * n) := h2N
        _ = (2 * n) * (n' - 1) := by ring
    have hn_eq : n = n' - 1 := Nat.mul_left_cancel (by omega : 0 < 2 * n) h2N'
    have hn'succ : n' = n + 1 := by omega
    rw [hn'succ] at hE
    have hdvd : n + 1 ∣ 2 * j * n := ⟨d, by rw [mul_comm (n + 1) d, ← hE]; ring⟩
    have hcop : Nat.Coprime (n + 1) n := by
      rw [Nat.coprime_comm]
      exact (Nat.coprime_self_add_right).mpr (by simp)
    have hdvd2 : n + 1 ∣ 2 * j := hcop.dvd_of_dvd_mul_right hdvd
    have hn'4 : n' ≤ 4 * j := by
      have : n + 1 ≤ 2 * j := Nat.le_of_dvd (by omega : 0 < 2 * j) hdvd2
      omega
    have hD : lieOrderDivisor .POmegaOdd n (3 ^ j) ≤ 3 ^ j + 1 := by
      simp only [lieOrderDivisor]
      have h3 : 3 ≤ 3 ^ j := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
    have hD' : lieOrderDivisor .PSL n' (3 ^ d) ≤ 4 * j :=
      le_trans (Nat.le_of_dvd hn' (cl24_D_PSL_dvd n' (3 ^ d))) hn'4
    exact (not_le_of_gt (cl24_digit_contra4 (by omega) hD hD')) hsize
  ·
    have hn4 : 4 ≤ n := hadm.2.2
    simp only [lieSylowExponent, cl24E] at h2N hE
    have h2N' : (2 * (n - 1)) * n = (2 * (n - 1)) * (n' - 1) := by
      calc (2 * (n - 1)) * n = 2 * (n * (n - 1)) := by ring
        _ = (n' - 1) * (2 * (n - 1)) := h2N
        _ = (2 * (n - 1)) * (n' - 1) := by ring
    have hn_eq : n = n' - 1 := Nat.mul_left_cancel (by omega : 0 < 2 * (n - 1)) h2N'
    have hn'succ : n' = n + 1 := by omega
    rw [hn'succ] at hE
    have hdvd1 : n + 1 ∣ 2 * j * (n - 1) := ⟨d, by rw [mul_comm (n + 1) d, ← hE]; ring⟩
    have hdvd2 : n + 1 ∣ 2 * j * (n + 1) := ⟨2 * j, by ring⟩
    have hdvd3 : n + 1 ∣ 4 * j := by
      have hsub := Nat.dvd_sub hdvd2 hdvd1
      have h4 : 2 * j * (n + 1) - 2 * j * (n - 1) = 4 * j := by
        rw [← Nat.mul_sub_left_distrib]
        have : n + 1 - (n - 1) = 2 := by omega
        rw [this]; ring
      rwa [h4] at hsub
    have hn'4 : n' ≤ 4 * j := by
      have : n + 1 ≤ 4 * j := Nat.le_of_dvd (by omega : 0 < 4 * j) hdvd3
      omega
    have hD : lieOrderDivisor .POmegaPlus n (3 ^ j) ≤ 3 ^ j + 1 := by
      simp only [lieOrderDivisor]
      have hg : Nat.gcd 4 ((3 ^ j) ^ n - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
      have h3 : 3 ≤ 3 ^ j := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
    have hD' : lieOrderDivisor .PSL n' (3 ^ d) ≤ 4 * j :=
      le_trans (Nat.le_of_dvd hn' (cl24_D_PSL_dvd n' (3 ^ d))) hn'4
    exact (not_le_of_gt (cl24_digit_contra4 (by omega) hD hD')) hsize
  ·
    have hn4 : 4 ≤ n := hadm.2.2
    simp only [lieSylowExponent, cl24E] at h2N hE
    have h2N' : (2 * n) * (n - 1) = (2 * n) * (n' - 1) := by
      calc (2 * n) * (n - 1) = 2 * (n * (n - 1)) := by ring
        _ = (n' - 1) * (2 * n) := h2N
        _ = (2 * n) * (n' - 1) := by ring
    have hnm1 : n - 1 = n' - 1 := Nat.mul_left_cancel (by omega : 0 < 2 * n) h2N'
    have hnn' : n' = n := by omega
    subst n'
    simp only [lieSylowExponent] at hN
    have hprodpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    have h2 : (n * (n - 1)) * (2 * j) = (n * (n - 1)) * d := by
      have hmul : 2 * (n * (n - 1) * j) = 2 * ((n * (n - 1) / 2) * d) := by rw [hN]
      calc (n * (n - 1)) * (2 * j) = 2 * (n * (n - 1) * j) := by ring
        _ = 2 * ((n * (n - 1) / 2) * d) := hmul
        _ = (2 * (n * (n - 1) / 2)) * d := by ring
        _ = (n * (n - 1)) * d := by rw [cl24_tri n]
    have hd_eq : 2 * j = d := Nat.mul_left_cancel hprodpos h2
    have hD4 : lieOrderDivisor .POmegaMinus n (3 ^ j) ≤ 4 := by
      simp only [lieOrderDivisor]
      exact Nat.gcd_le_left _ (by norm_num)
    have hD_even : 2 ∣ lieOrderDivisor .POmegaMinus n (3 ^ j) := by
      simp only [lieOrderDivisor]
      apply Nat.dvd_gcd (by norm_num : (2 : ℕ) ∣ 4)
      have hodd : Odd ((3 : ℕ) ^ j) := (show Odd (3 : ℕ) by norm_num).pow
      exact even_iff_two_dvd.mp (hodd.pow.add_one)
    have hD'dvd : lieOrderDivisor .PSL n (3 ^ d) ∣ 3 ^ (2 * j) - 1 := by
      rw [← hd_eq]
      exact cl24_D_PSL_dvd_sub n (3 ^ (2 * j))
    have hm_eq : 3 ^ (2 * j) = (3 ^ (2 * j) - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))).symm
    have h9 : 8 ≤ 3 ^ (2 * j) - 1 := by
      have : 9 ≤ 3 ^ (2 * j) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hlt : 3 ^ (2 * j) - 1 < 2 * lieOrderDivisor .PSL n (3 ^ d) := by
      rw [hm_eq] at hsize
      omega
    have hD'eq : lieOrderDivisor .PSL n (3 ^ d) = 3 ^ (2 * j) - 1 :=
      (Nat.eq_of_dvd_of_lt_two_mul (a := 3 ^ (2 * j) - 1)
        (b := lieOrderDivisor .PSL n (3 ^ d)) (by omega) hD'dvd hlt).symm
    obtain ⟨s, s', hs, hs', hne, hdvdX⟩ := hX
    have hD'cast : (lieOrderDivisor .PSL n (3 ^ d) : ℤ) = (3 : ℤ) ^ (2 * j) - 1 := by
      rw [hD'eq, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_one,
        Nat.cast_pow]
      norm_num
    have hdvd_sum :
        (3 : ℤ) ^ (2 * j) ∣ (s + s' * (lieOrderDivisor .POmegaMinus n (3 ^ j) : ℤ)) := by
      have hA : s * (lieOrderDivisor .PSL n (3 ^ d) : ℤ) -
            s' * (lieOrderDivisor .POmegaMinus n (3 ^ j) : ℤ) =
          s * (3 : ℤ) ^ (2 * j) -
            (s + s' * (lieOrderDivisor .POmegaMinus n (3 ^ j) : ℤ)) := by
        rw [hD'cast]; ring
      rw [hA] at hdvdX
      have hq : (3 : ℤ) ^ (2 * j) ∣ s * (3 : ℤ) ^ (2 * j) := ⟨s, by ring⟩
      have hboth := dvd_sub hq hdvdX
      convert hboth using 1
      ring
    have hq9 : (9 : ℤ) ≤ (3 : ℤ) ^ (2 * j) := by
      calc (9 : ℤ) = (3 : ℤ) ^ 2 := by norm_num
        _ ≤ (3 : ℤ) ^ (2 * j) := pow_le_pow_right₀ (by norm_num) (by omega)
    have habs : |s + s' * (lieOrderDivisor .POmegaMinus n (3 ^ j) : ℤ)| < (3 : ℤ) ^ (2 * j) := by
      have h5 : |s + s' * (lieOrderDivisor .POmegaMinus n (3 ^ j) : ℤ)| ≤ 5 := by
        have hD4z : (lieOrderDivisor .POmegaMinus n (3 ^ j) : ℤ) ≤ 4 := by
          exact_mod_cast hD4
        rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;>
          simp only [one_mul, neg_mul, neg_neg] <;>
          rw [abs_le] <;> constructor <;> omega
      linarith
    have hzero := Int.eq_zero_of_abs_lt_dvd hdvd_sum habs
    have hD1 : (lieOrderDivisor .POmegaMinus n (3 ^ j) : ℤ) = 1 := by
      rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;>
        simp only [one_mul, neg_mul, neg_neg] at hzero ⊢ <;> omega
    have : lieOrderDivisor .POmegaMinus n (3 ^ j) = 1 := by exact_mod_cast hD1
    obtain ⟨k, hk⟩ := hD_even
    omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
