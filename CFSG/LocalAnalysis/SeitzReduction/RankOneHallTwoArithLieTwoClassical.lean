module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithLieTwoBasic

public section

namespace CFSG.SeitzReduction.RankOne.LieTwo

open CFSG.Timmesfeld

theorem psl_ppd {m f e h k : ℕ} (hk2 : 2 ≤ k) (hkm : k ≤ m) (hf : 1 ≤ f) (h6 : f * k ≠ 6)
    (hcof : ∏ i ∈ Finset.Icc 2 m, ((2 ^ f) ^ i - 1) = h * Nat.gcd m (2 ^ f - 1))
    (he : e = m * (m - 1) / 2 * f) (hkN : ¬ k ∣ m * (m - 1) / 2)
    (hrN : ∀ r, IsPrimitivePrimeDivisor r (f * k) → ¬ r ∣ m * (m - 1) / 2)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hfk : 2 ≤ f * k := le_trans hk2 (Nat.le_mul_of_pos_left k hf)
  refine false_of_ppd hfk h6 (by rw [he, mul_comm]) hkN (fun r hr => ?_) hrN hdiv
  refine ppd_dvd_left hr (by omega) (g := Nat.gcd m (2 ^ f - 1)) (j := 1)
    (by rw [pow_one]; exact Nat.gcd_dvd_right _ _)
    (fun h1 => absurd (Nat.le_of_dvd one_pos h1) (by omega)) ?_
  rw [← hcof]
  exact (ppd_dvd_pow_sub_one hr dvd_rfl).trans
    (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ i - 1) (Finset.mem_Icc.2 ⟨hk2, hkm⟩))

theorem psl {m f e h : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f)
    (hcof : ∏ i ∈ Finset.Icc 2 m, ((2 ^ f) ^ i - 1) = h * Nat.gcd m (2 ^ f - 1))
    (he : e = m * (m - 1) / 2 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : m = 3 ∧ f = 1 := by
  have hN2 := two_mul_tri m
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · interval_cases m
    ·
      exfalso
      have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := gcd_two_pow_eq_one (a := 1)
        (by simpa using odd_two_pow_pow_sub_one (a := 1) hf le_rfl)
      simp only [Finset.Icc_self, Finset.prod_singleton, hg, mul_one] at hcof
      have he' : e = f := by rw [he]; norm_num
      rw [he', ← hcof] at hdiv
      have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
      have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
        rw [← one_pow 2, Nat.sq_sub_sq, one_pow, mul_comm]
      rw [hfac] at hdiv
      have h1 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mul_dvd_mul_left (by omega) hdiv)
      have := @Nat.lt_two_pow_self f
      omega
    ·
      rcases (by omega : f = 1 ∨ f = 3 ∨ (f ≠ 1 ∧ f ≠ 3)) with rfl | rfl | ⟨hf1, hf3⟩
      · exact ⟨rfl, rfl⟩
      ·
        exfalso
        have hc : ∏ i ∈ Finset.Icc 2 3, ((2 ^ 3) ^ i - 1) = 32193 := by decide
        have hg : Nat.gcd 3 (2 ^ 3 - 1) = 1 := by decide
        rw [hc, hg, mul_one] at hcof
        have he' : e = 9 := by rw [he]
        rw [he', ← hcof] at hdiv
        exact absurd hdiv (by decide)
      · exfalso
        refine psl_ppd (k := 2) le_rfl (by norm_num) hf (by omega) hcof he (by decide)
          (fun r hr => not_dvd_tri hr.prime (by norm_num) ?_) hdiv
        have := lt_of_isPrimitivePrimeDivisor hr (by omega)
        omega
  · exfalso
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    ·
      by_cases h61 : m = 6 ∧ f = 1
      ·
        obtain ⟨rfl, rfl⟩ := h61
        have hc : ∏ i ∈ Finset.Icc 2 6, ((2 ^ 1) ^ i - 1) = 615195 := by decide
        have hg : Nat.gcd 6 (2 ^ 1 - 1) = 1 := by decide
        rw [hc, hg, mul_one] at hcof
        have he' : e = 15 := by rw [he]
        rw [he', ← hcof] at hdiv
        exact absurd hdiv (by decide)
      · have hfm : m ≤ f * m := Nat.le_mul_of_pos_left m hf
        refine psl_ppd (k := m) (by omega) le_rfl hf ?_ hcof he ?_
          (fun r hr => not_dvd_tri hr.prime hm ?_) hdiv
        · intro h6
          rcases Nat.lt_or_ge f 2 with hf2 | hf2
          · obtain rfl : f = 1 := by omega
            omega
          · have : 2 * m ≤ f * m := Nat.mul_le_mul_right m hf2
            omega
        · rintro ⟨c, hc⟩
          have h1 : m * (m - 1) = m * (2 * c) := by rw [← hN2, hc]; ring
          have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
          omega
        · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
          omega
    ·
      rcases Nat.lt_or_ge f 2 with hf2 | hf2
      ·
        obtain rfl : f = 1 := by omega
        refine psl_ppd (k := m - 2) (by omega) (by omega) le_rfl (by omega) hcof he ?_
          (fun r hr => ?_) hdiv
        · intro hd
          have h1 : m - 2 ∣ m * (m - 1) := hd.trans (tri_dvd m)
          have h2 : m * (m - 1) = (m - 2) * (m + 1) + 2 := by
            obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
            rw [show i + 2 - 1 = i + 1 by omega, show i + 2 - 2 = i by omega]
            ring
          rw [h2] at h1
          have := Nat.le_of_dvd (by norm_num) ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h1)
          omega
        ·
          have hK : 0 < 1 * (m - 2) := by omega
          have hlt := lt_of_isPrimitivePrimeDivisor hr hK
          have hd := dvd_sub_one_of_isPrimitivePrimeDivisor hr hK
          intro hrN
          have hle := prime_le_of_dvd_mul_sub_one hr.prime hm (hrN.trans (tri_dvd m))
          rcases (by omega : r = m - 1 ∨ r = m) with h1 | h1
          · have h2 : 2 ∣ r := ⟨j, by omega⟩
            rcases (Nat.dvd_prime hr.prime).1 h2 with h3 | h3 <;> omega
          · rw [h1, one_mul, show m - 1 = (m - 2) + 1 by omega] at hd
            have := Nat.le_of_dvd one_pos ((Nat.dvd_add_right dvd_rfl).1 hd)
            omega
      ·
        have hfm : 2 * (m - 1) ≤ f * (m - 1) := Nat.mul_le_mul_right _ hf2
        refine psl_ppd (k := m - 1) (by omega) (by omega) hf (by omega) hcof he ?_
          (fun r hr => not_dvd_tri hr.prime hm ?_) hdiv
        · rintro ⟨c, hc⟩
          have h1 : (m - 1) * m = (m - 1) * (2 * c) := by rw [mul_comm, ← hN2, hc]; ring
          have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
          omega
        · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
          omega

theorem psu_ppd {m f e h k a : ℕ} (hk3 : 3 ≤ k) (ha : a ∈ Finset.Icc 2 m) (hf : 1 ≤ f)
    (h6 : f * k ≠ 6)
    (hterm : ∀ r, IsPrimitivePrimeDivisor r (f * k) →
      r ∣ (if Even a then (2 ^ f) ^ a - 1 else (2 ^ f) ^ a + 1))
    (hcof : ∏ i ∈ Finset.Icc 2 m, (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) =
      h * Nat.gcd m (2 ^ f + 1))
    (he : e = m * (m - 1) / 2 * f) (hkN : ¬ k ∣ m * (m - 1) / 2)
    (hrN : ∀ r, IsPrimitivePrimeDivisor r (f * k) → ¬ r ∣ m * (m - 1) / 2)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hfk : 2 ≤ f * k := le_trans (by omega) (Nat.le_mul_of_pos_left k hf)
  refine false_of_ppd hfk h6 (by rw [he, mul_comm]) hkN (fun r hr => ?_) hrN hdiv
  refine ppd_dvd_left hr (by omega) (g := Nat.gcd m (2 ^ f + 1)) (j := 2)
    ((Nat.gcd_dvd_right _ _).trans (succ_dvd_sq_sub_one _))
    (fun h2 => absurd (Nat.le_of_dvd two_pos h2) (by omega)) ?_
  rw [← hcof]
  exact (hterm r hr).trans (Finset.dvd_prod_of_mem
    (fun i => if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) ha)

theorem psu {m f e h : ℕ} (hm : 3 ≤ m) (hf : 1 ≤ f)
    (hcof : ∏ i ∈ Finset.Icc 2 m, (if Even i then (2 ^ f) ^ i - 1 else (2 ^ f) ^ i + 1) =
      h * Nat.gcd m (2 ^ f + 1))
    (he : e = m * (m - 1) / 2 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hN2 := two_mul_tri m
  rcases Nat.even_or_odd m with hme | hmo
  ·
    obtain ⟨j, hj⟩ := hme
    by_cases h61 : m = 6 ∧ f = 1
    ·
      obtain ⟨rfl, rfl⟩ := h61
      have hc : ∏ i ∈ Finset.Icc 2 6,
          (if Even i then (2 ^ 1) ^ i - 1 else (2 ^ 1) ^ i + 1) = 841995 := by decide
      have hg : Nat.gcd 6 (2 ^ 1 + 1) = 3 := by decide
      rw [hc, hg] at hcof
      obtain rfl : h = 280665 := by omega
      have he' : e = 15 := by rw [he]
      rw [he'] at hdiv
      exact absurd hdiv (by decide)
    · have hfm : m ≤ f * m := Nat.le_mul_of_pos_left m hf
      refine psu_ppd (k := m) (a := m) (by omega) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) hf ?_
        (fun r hr => ?_) hcof he ?_ (fun r hr => not_dvd_tri hr.prime (by omega) ?_) hdiv
      · intro h6
        rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · obtain rfl : f = 1 := by omega
          omega
        · have : 2 * m ≤ f * m := Nat.mul_le_mul_right m hf2
          omega
      · rw [ite_eq_left ⟨j, hj⟩]
        exact ppd_dvd_pow_sub_one hr dvd_rfl
      · rintro ⟨c, hc⟩
        have h1 : m * (m - 1) = m * (2 * c) := by rw [← hN2, hc]; ring
        have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
        omega
      · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
        omega
  · have hmo' : ¬ Even m := Nat.not_even_iff_odd.2 hmo
    obtain ⟨j, hj⟩ := hmo
    rcases Nat.lt_or_ge (m % 4) 2 with h4 | h4
    ·
      by_cases h51 : m = 5 ∧ f = 1
      ·
        obtain ⟨rfl, rfl⟩ := h51
        have hc : ∏ i ∈ Finset.Icc 2 5,
            (if Even i then (2 ^ 1) ^ i - 1 else (2 ^ 1) ^ i + 1) = 13365 := by decide
        have hg : Nat.gcd 5 (2 ^ 1 + 1) = 1 := by decide
        rw [hc, hg, mul_one] at hcof
        have he' : e = 10 := by rw [he]
        rw [he', ← hcof] at hdiv
        exact absurd hdiv (by decide)
      · have hfm : 2 * (m - 2) ≤ f * (2 * (m - 2)) := Nat.le_mul_of_pos_left _ hf
        refine psu_ppd (k := 2 * (m - 2)) (a := m - 2) (by omega)
          (Finset.mem_Icc.2 ⟨by omega, by omega⟩) hf ?_ (fun r hr => ?_) hcof he ?_
          (fun r hr => not_dvd_tri hr.prime (by omega) ?_) hdiv
        · intro h6
          rcases Nat.lt_or_ge f 2 with hf2 | hf2
          · obtain rfl : f = 1 := by omega
            omega
          · have : 2 * (2 * (m - 2)) ≤ f * (2 * (m - 2)) := Nat.mul_le_mul_right _ hf2
            omega
        · rw [ite_eq_right (by rw [Nat.not_even_iff_odd]; exact ⟨j - 1, by omega⟩)]
          exact ppd_dvd_pow_add_one hr (Nat.mul_pos (by omega) (by omega))
        · intro hd
          have h1 : m - 2 ∣ m * (m - 1) :=
            ((Dvd.intro_left 2 rfl).trans hd).trans (tri_dvd m)
          have h2 : m * (m - 1) = (m - 2) * (m + 1) + 2 := by
            obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
            rw [show i + 2 - 1 = i + 1 by omega, show i + 2 - 2 = i by omega]
            ring
          rw [h2] at h1
          have := Nat.le_of_dvd (by norm_num) ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h1)
          omega
        · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
          omega
    ·
      by_cases h31 : m = 3 ∧ f = 1
      ·
        obtain ⟨rfl, rfl⟩ := h31
        have hc : ∏ i ∈ Finset.Icc 2 3,
            (if Even i then (2 ^ 1) ^ i - 1 else (2 ^ 1) ^ i + 1) = 27 := by decide
        have hg : Nat.gcd 3 (2 ^ 1 + 1) = 3 := by decide
        rw [hc, hg] at hcof
        obtain rfl : h = 9 := by omega
        have he' : e = 3 := by omega
        rw [he'] at hdiv
        exact absurd hdiv (by decide)
      have hfm : 2 * m ≤ f * (2 * m) := Nat.le_mul_of_pos_left _ hf
      refine psu_ppd (k := 2 * m) (a := m) (by omega) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) hf
        ?_ (fun r hr => ?_) hcof he ?_ (fun r hr => not_dvd_tri hr.prime (by omega) ?_) hdiv
      · intro h6
        rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · obtain rfl : f = 1 := by omega
          exact h31 ⟨by omega, rfl⟩
        · have : 2 * (2 * m) ≤ f * (2 * m) := Nat.mul_le_mul_right _ hf2
          omega
      · rw [ite_eq_right hmo']
        exact ppd_dvd_pow_add_one hr (Nat.mul_pos (by omega) (by omega))
      · rintro ⟨c, hc⟩
        have h1 : m * (m - 1) = m * (4 * c) := by rw [← hN2, hc]; ring
        have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
        omega
      · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
        omega

theorem psp_ppd {m f e h k a : ℕ} (hk : 2 ≤ f * k) (h6 : f * k ≠ 6) (ha : a ∈ Finset.Icc 1 m)
    (hka : k ∣ 2 * a) (hcof : ∏ i ∈ Finset.Icc 1 m, ((2 ^ f) ^ (2 * i) - 1) = h)
    (he : e = m ^ 2 * f) (hkN : ¬ k ∣ m ^ 2)
    (hrN : ∀ r, IsPrimitivePrimeDivisor r (f * k) → ¬ r ∣ m ^ 2)
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  refine false_of_ppd hk h6 (by rw [he, mul_comm]) hkN (fun r hr => ?_) hrN hdiv
  rw [← hcof]
  exact (ppd_dvd_pow_sub_one hr hka).trans
    (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) ha)

theorem psp {m f e h : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f)
    (hcof : ∏ i ∈ Finset.Icc 1 m, ((2 ^ f) ^ (2 * i) - 1) = h * Nat.gcd 2 (2 ^ f - 1))
    (he : e = m ^ 2 * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := gcd_two_pow_eq_one (a := 1)
    (by simpa using odd_two_pow_pow_sub_one (a := 1) hf le_rfl)
  rw [hg, mul_one] at hcof
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    obtain rfl : m = 2 := by omega
    rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
      Finset.prod_pair (by norm_num)] at hcof
    have h2e : 2 ^ e = (2 ^ f) ^ 4 := by rw [he, ← pow_mul]; ring_nf
    rw [h2e, ← hcof, mul_comm] at hdiv
    have hd := Nat.dvd_of_mul_dvd_mul_left
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega)))) hdiv
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    ·
      obtain rfl : f = 1 := by omega
      rw [he] at hd
      exact absurd hd (by decide)
    have h1 := Nat.le_of_dvd (by rw [he]; positivity) hd
    have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
    have h8 : 4 * (2 * f) ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul h4 (two_mul_le_two_pow f)
    rw [he] at h1
    simp only [mul_one, sq] at h1
    omega
  · rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    ·
      by_cases h41 : m = 4 ∧ f = 1
      ·
        obtain ⟨rfl, rfl⟩ := h41
        have hc : ∏ i ∈ Finset.Icc 1 4, ((2 ^ 1) ^ (2 * i) - 1) = 722925 := by decide
        rw [hc] at hcof
        have he' : e = 16 := by rw [he]; norm_num
        rw [he', ← hcof] at hdiv
        exact absurd hdiv (by decide)
      · have hfm : 2 * (m - 1) ≤ f * (2 * (m - 1)) := Nat.le_mul_of_pos_left _ hf
        refine psp_ppd (k := 2 * (m - 1)) (a := m - 1) (by omega) ?_
          (Finset.mem_Icc.2 ⟨by omega, by omega⟩) dvd_rfl hcof he ?_
          (fun r hr => not_dvd_sq hr.prime (by omega) ?_) hdiv
        · intro h6
          rcases Nat.lt_or_ge f 2 with hf2 | hf2
          · obtain rfl : f = 1 := by omega
            omega
          · have : 2 * (2 * (m - 1)) ≤ f * (2 * (m - 1)) := Nat.mul_le_mul_right _ hf2
            omega
        · intro hd
          have h1 : m - 1 ∣ m ^ 2 := (Dvd.intro_left 2 rfl).trans hd
          have h2 : m ^ 2 = (m - 1) * (m + 1) + 1 := by
            obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
            rw [show i + 1 - 1 = i by omega]
            ring
          rw [h2] at h1
          have := Nat.le_of_dvd one_pos ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h1)
          omega
        · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
          omega
    ·
      by_cases h31 : m = 3 ∧ f = 1
      ·
        obtain ⟨rfl, rfl⟩ := h31
        have hc : ∏ i ∈ Finset.Icc 1 3, ((2 ^ 1) ^ (2 * i) - 1) = 2835 := by decide
        rw [hc] at hcof
        have he' : e = 9 := by rw [he]; norm_num
        rw [he', ← hcof] at hdiv
        exact absurd hdiv (by decide)
      · have hfm : 2 * m ≤ f * (2 * m) := Nat.le_mul_of_pos_left _ hf
        refine psp_ppd (k := 2 * m) (a := m) (by omega) ?_
          (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) dvd_rfl hcof he ?_
          (fun r hr => not_dvd_sq hr.prime (by omega) ?_) hdiv
        · intro h6
          rcases Nat.lt_or_ge f 2 with hf2 | hf2
          · obtain rfl : f = 1 := by omega
            omega
          · have : 2 * (2 * m) ≤ f * (2 * m) := Nat.mul_le_mul_right _ hf2
            omega
        · rintro ⟨c, hc⟩
          have h1 : m * m = m * (2 * c) := by rw [← sq, hc]; ring
          have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
          omega
        · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
          omega

theorem omega_ppd {m f e h k a c : ℕ} (hk : 2 ≤ f * k) (h6 : f * k ≠ 6)
    (ha : a ∈ Finset.Icc 1 (m - 1)) (hka : k ∣ 2 * a)
    (hcof : c * ∏ i ∈ Finset.Icc 1 (m - 1), ((2 ^ f) ^ (2 * i) - 1) = h)
    (he : e = m * (m - 1) * f) (hkN : ¬ k ∣ m * (m - 1))
    (hrN : ∀ r, IsPrimitivePrimeDivisor r (f * k) → ¬ r ∣ m * (m - 1))
    (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  refine false_of_ppd hk h6 (by rw [he, mul_comm]) hkN (fun r hr => ?_) hrN hdiv
  rw [← hcof]
  exact ((ppd_dvd_pow_sub_one hr hka).trans
    (Finset.dvd_prod_of_mem (fun i => (2 ^ f) ^ (2 * i) - 1) ha)).mul_left c

theorem not_two_mul_pred_dvd {m : ℕ} (hm : 3 ≤ m) (hmo : Odd m) :
    ¬ 2 * (m - 1) ∣ m * (m - 1) := by
  rintro ⟨c, hc⟩
  have h1 : (m - 1) * m = (m - 1) * (2 * c) := by rw [mul_comm, hc]; ring
  have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
  obtain ⟨j, hj⟩ := hmo
  omega

theorem omegaPlus {m f e h : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ m - 1) * ∏ i ∈ Finset.Icc 1 (m - 1), ((2 ^ f) ^ (2 * i) - 1) =
      h * Nat.gcd 4 ((2 ^ f) ^ m - 1))
    (he : e = m * (m - 1) * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hg : Nat.gcd 4 ((2 ^ f) ^ m - 1) = 1 :=
    gcd_two_pow_eq_one (a := 2) (odd_two_pow_pow_sub_one hf (by omega))
  rw [hg, mul_one] at hcof
  rcases Nat.lt_or_ge m 5 with hm5 | hm5
  ·
    obtain rfl : m = 4 := by omega
    rw [show Finset.Icc 1 (4 - 1) = ({1, 2, 3} : Finset ℕ) by decide,
      Finset.prod_insert (by decide), Finset.prod_pair (by norm_num)] at hcof
    set q := 2 ^ f with hq
    have hq2 : 2 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
    have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
    have hX : 0 < q ^ 4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
    have h2e : 2 ^ e - 1 = (q ^ 4 - 1) * (q ^ 8 + q ^ 4 + 1) := by
      rw [he, show 4 * (4 - 1) * f = f * 12 by ring, pow_mul, ← hq]
      zify [h4, h12]
      ring
    have hh : h = (q ^ 4 - 1) * ((q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 6 - 1))) := by
      rw [← hcof]; ring_nf
    rw [h2e, hh, mul_assoc] at hdiv
    have h1 := Nat.dvd_of_mul_dvd_mul_left hX hdiv
    have h2 : q ^ 4 - 1 ∣ (q ^ 8 + q ^ 4 + 1) * e := (dvd_mul_right _ _).trans h1
    have h3 : (q ^ 8 + q ^ 4 + 1) * e = (q ^ 4 - 1) * ((q ^ 4 + 2) * e) + 3 * e := by
      zify [h4]
      ring
    rw [h3] at h2
    have h5 := (Nat.dvd_add_right (dvd_mul_right _ _)).1 h2
    have he' : e = 12 * f := by rw [he]
    rw [he'] at h5
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      rw [hq] at h5
      exact absurd h5 (by decide)
    · have h6 := Nat.le_of_dvd (by omega) h5
      have hq4 : 4 ≤ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      have h8 : 4 * (2 * f) ≤ q * q := Nat.mul_le_mul hq4 (two_mul_le_two_pow f)
      have h16 : 4 * 4 ≤ q * q := Nat.mul_le_mul hq4 hq4
      have h128 : 4 * 4 * (4 * (2 * f)) ≤ q * q * (q * q) := Nat.mul_le_mul h16 h8
      have hq4' : q ^ 4 = q * q * (q * q) := by ring
      omega
  · rcases Nat.even_or_odd m with ⟨j, hj⟩ | hmo
    ·
      have hfm : 2 * (m - 2) ≤ f * (2 * (m - 2)) := Nat.le_mul_of_pos_left _ hf
      refine omega_ppd (k := 2 * (m - 2)) (a := m - 2) (by omega) (by omega)
        (Finset.mem_Icc.2 ⟨by omega, by omega⟩) dvd_rfl hcof he ?_
        (fun r hr => not_dvd_mul_sub_one hr.prime (by omega) ?_) hdiv
      · intro hd
        have h1 : m - 2 ∣ m * (m - 1) := (Dvd.intro_left 2 rfl).trans hd
        have h2 : m * (m - 1) = (m - 2) * (m + 1) + 2 := by
          obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
          rw [show i + 2 - 1 = i + 1 by omega, show i + 2 - 2 = i by omega]
          ring
        rw [h2] at h1
        have := Nat.le_of_dvd (by norm_num) ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h1)
        omega
      · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
        omega
    ·
      have hfm : 2 * (m - 1) ≤ f * (2 * (m - 1)) := Nat.le_mul_of_pos_left _ hf
      refine omega_ppd (k := 2 * (m - 1)) (a := m - 1) (by omega) (by omega)
        (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) dvd_rfl hcof he
        (not_two_mul_pred_dvd (by omega) hmo)
        (fun r hr => not_dvd_mul_sub_one hr.prime (by omega) ?_) hdiv
      have := lt_of_isPrimitivePrimeDivisor hr (by omega)
      omega

theorem omegaMinus {m f e h : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    (hcof : ((2 ^ f) ^ m + 1) * ∏ i ∈ Finset.Icc 1 (m - 1), ((2 ^ f) ^ (2 * i) - 1) =
      h * Nat.gcd 4 ((2 ^ f) ^ m + 1))
    (he : e = m * (m - 1) * f) (hdiv : h ∣ (2 ^ e - 1) * e) : False := by
  have hg : Nat.gcd 4 ((2 ^ f) ^ m + 1) = 1 :=
    gcd_two_pow_eq_one (a := 2) (odd_two_pow_pow_add_one hf (by omega))
  rw [hg, mul_one] at hcof
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | hmo
  ·
    have hfm : 2 * m ≤ f * (2 * m) := Nat.le_mul_of_pos_left _ hf
    refine false_of_ppd (f := f) (k := 2 * m) (N := m * (m - 1)) (by omega) (by omega)
      (by rw [he, mul_comm]) ?_
      (fun r hr => ?_) (fun r hr => not_dvd_mul_sub_one hr.prime (by omega) ?_) hdiv
    · rintro ⟨c, hc⟩
      have h1 : m * (m - 1) = m * (2 * c) := by rw [hc]; ring
      have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
      omega
    · rw [← hcof]
      exact (ppd_dvd_pow_add_one hr (Nat.mul_pos (by omega) (by omega))).mul_right _
    · have := lt_of_isPrimitivePrimeDivisor hr (by omega)
      omega
  ·
    have hm5 : 5 ≤ m := by obtain ⟨j, hj⟩ := hmo; omega
    have hfm : 2 * (m - 1) ≤ f * (2 * (m - 1)) := Nat.le_mul_of_pos_left _ hf
    refine omega_ppd (k := 2 * (m - 1)) (a := m - 1) (by omega) (by omega)
      (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) dvd_rfl hcof he
      (not_two_mul_pred_dvd (by omega) hmo)
      (fun r hr => not_dvd_mul_sub_one hr.prime (by omega) ?_) hdiv
    have := lt_of_isPrimitivePrimeDivisor hr (by omega)
    omega

end CFSG.SeitzReduction.RankOne.LieTwo
