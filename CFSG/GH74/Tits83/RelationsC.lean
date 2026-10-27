module

public import CFSG.GH74.Tits83.RelationsA2

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

private theorem eq_of_conj_eq {m a b : G} (hm : m * m = 1) (h : a = m * b * m⁻¹) :
    b = m * a * m⁻¹ := by
  have hm' : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm
  rw [h, hm']
  calc b = (m * m) * b * (m * m) := by rw [hm]; group
    _ = m * (m * b * m) * m := by group

theorem comm_X1_X8 (t u : F.K) :
    ⁅F.X 1 t, F.X 8 u⁆ =
      F.X 2 (t * u) * F.X 3 (F.sigma t * t * F.sigma u * u ^ 2) *
        (F.X 4 (F.sigma t * F.sigma u * u))⁻¹ *
        F.X 5 (F.sigma t * t * F.sigma u ^ 2 * u ^ 2) *
        F.X' 6 (F.sigma t * t * F.sigma u ^ 2 * u ^ 3) * F.X 7 (t * F.sigma u * u ^ 2) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hst : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  have hsu : F.sigma u ≠ 0 := (map_ne_zero F.sigma).2 hu
  set a : F.K := t * u with ha
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero ht hu
  set dd : F.K := F.sigma t * t * F.sigma u * u ^ 2 with hdd
  have hdd0 : dd ≠ 0 := by
    rw [hdd]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hst ht) hsu) (pow_ne_zero 2 hu)
  set f : F.K := F.sigma t * F.sigma u * u with hf
  have hf0 : f ≠ 0 := by
    rw [hf]
    exact mul_ne_zero (mul_ne_zero hst hsu) hu
  set ff : F.K := F.sigma t * t * F.sigma u ^ 2 * u ^ 2 with hff
  have hff0 : ff ≠ 0 := by
    rw [hff]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hst ht) (pow_ne_zero 2 hsu)) (pow_ne_zero 2 hu)
  set hh : F.K := F.sigma t * t * F.sigma u ^ 2 * u ^ 3 with hhh
  have hhh0 : hh ≠ 0 := by
    rw [hhh]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hst ht) (pow_ne_zero 2 hsu)) (pow_ne_zero 3 hu)
  obtain ⟨s, hs1, hs8, hmem, hrec, hC, hR⟩ :=
    T.lemma29 (by norm_num : 3 ≤ 8) (F.X_mem 1 t) (F.X_ne_one 1 ht)
      (F.X_mem 8 u) (F.X_ne_one 8 hu)
  have h1 : s 1 = F.X 1 t := by
    rw [hs1, F.X_inv_odd (j := 1) (by decide) t]
  have h8 : s 8 = F.X 8 u := hs8
  have h2 : s 2 = F.X 2 a := by
    have hm1 : T.mu 1 (F.X 1 t) * T.mu 1 (F.X 1 t) = 1 :=
      F.mu_X_mul_self 1 ht
    have hR1 := hR 1 (by norm_num)
    norm_num at hR1
    rw [h1, h8] at hR1
    have hconj : T.mu 1 (F.X 1 t) * F.X 8 u * (T.mu 1 (F.X 1 t))⁻¹ = F.X 2 a := by
      have := F.mu_X_odd_conj_X (i := 1) (t := t) (by decide) ht (j := 8) u
      norm_num [wtX] at this
      simpa [ha] using this
    have := eq_of_conj_eq hm1 hR1
    rwa [hconj] at this
  have h9 : s 9 = F.X 9 t⁻¹ := by
    have h := hrec 1 (by norm_num)
    norm_num at h
    rw [h, h1, F.nu'_X_odd (j := 1) (t := t) (by decide) ht]
    norm_num
  have h3 : s 3 = F.X 3 dd := by
    have hm2 : T.mu 2 (F.X 2 a) * T.mu 2 (F.X 2 a) = 1 :=
      F.mu_X_mul_self 2 ha0
    have hR2 := hR 2 (by norm_num)
    norm_num at hR2
    rw [h2, h9] at hR2
    set c : F.K := (F.sigma a * a)⁻¹ with hc
    have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero ((map_ne_zero F.sigma).2 ha0) ha0)
    have hc_eq : T.mu 2 (F.X 2 a) = T.mu 10 (F.X' 10 c) := by
      rw [F.mu_X_even (i := 2) (t := a) (by decide) ha0, hc]
      norm_num
    have hconj : T.mu 2 (F.X 2 a) * F.X 9 t⁻¹ * (T.mu 2 (F.X 2 a))⁻¹ = F.X 3 dd := by
      rw [hc_eq]
      have := F.mu_X'_conj_X (i := 10) (t := c) (by decide) hc0 (j := 9) (t⁻¹)
      norm_num [wtX] at this
      rw [this, show (19 : ℤ) = 3 + 16 by norm_num, F.X_add_sixteen]
      congr 1
      have hsc : F.sigma c = (a ^ 2 * F.sigma a)⁻¹ := by
        rw [hc, map_inv₀, map_mul, F.sigma_sigma]
      rw [hsc, ha, map_mul, hdd]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm2 hR2
    rwa [hconj] at this
  have h10 : s 10 = (F.X 10 a⁻¹)⁻¹ := by
    have h := hrec 2 (by norm_num)
    norm_num at h
    rw [h, h2, F.nu'_X_even (j := 2) (t := a) (by decide) ha0]
    norm_num
  have h4 : s 4 = (F.X 4 f)⁻¹ := by
    have hm3 : T.mu 3 (F.X 3 dd) * T.mu 3 (F.X 3 dd) = 1 :=
      F.mu_X_mul_self 3 hdd0
    have hR3 := hR 3 (by norm_num)
    norm_num at hR3
    rw [h3, h10] at hR3
    have hconj : T.mu 3 (F.X 3 dd) * (F.X 10 a⁻¹)⁻¹ * (T.mu 3 (F.X 3 dd))⁻¹ =
        (F.X 4 f)⁻¹ := by
      have hg : T.mu 3 (F.X 3 dd) * F.X 10 a⁻¹ * (T.mu 3 (F.X 3 dd))⁻¹ =
          F.X 4 (dd * a⁻¹) := by
        have := F.mu_X_odd_conj_X (i := 3) (t := dd) (by decide) hdd0 (j := 10) (a⁻¹)
        norm_num [wtX] at this
        simpa using this
      calc T.mu 3 (F.X 3 dd) * (F.X 10 a⁻¹)⁻¹ * (T.mu 3 (F.X 3 dd))⁻¹
          = (T.mu 3 (F.X 3 dd) * F.X 10 a⁻¹ * (T.mu 3 (F.X 3 dd))⁻¹)⁻¹ := by group
        _ = (F.X 4 (dd * a⁻¹))⁻¹ := by rw [hg]
        _ = (F.X 4 f)⁻¹ := by
            congr 1
            rw [hdd, hf, ha]
            field_simp [ht, hu]
    have := eq_of_conj_eq hm3 hR3
    rwa [hconj] at this
  have h11 : s 11 = F.X 11 dd⁻¹ := by
    have h := hrec 3 (by norm_num)
    norm_num at h
    rw [h, h3, F.nu'_X_odd (j := 3) (t := dd) (by decide) hdd0]
    norm_num
  set c4 : F.K := (F.sigma f * f)⁻¹ with hc4
  have hc40 : c4 ≠ 0 := inv_ne_zero (mul_ne_zero ((map_ne_zero F.sigma).2 hf0) hf0)
  have h5 : s 5 = F.X 5 ff := by
    have hm4 : T.mu 4 (F.X 4 f) * T.mu 4 (F.X 4 f) = 1 :=
      F.mu_X_mul_self 4 hf0
    have hm4inv : T.mu 4 ((F.X 4 f)⁻¹) = T.mu 4 (F.X 4 f) := by
      rw [T.mu_inv (i := 4) (u := F.X 4 f) (by norm_num : 3 ≤ 8)
        (F.X_mem 4 f) (F.X_ne_one 4 hf0)]
      exact inv_eq_of_mul_eq_one_right hm4
    have hR4 := hR 4 (by norm_num)
    norm_num at hR4
    rw [h4, h11, hm4inv] at hR4
    have hc4_eq : T.mu 4 (F.X 4 f) = T.mu 12 (F.X' 12 c4) := by
      rw [F.mu_X_even (i := 4) (t := f) (by decide) hf0, hc4]
      norm_num
    have hconj : T.mu 4 (F.X 4 f) * F.X 11 dd⁻¹ * (T.mu 4 (F.X 4 f))⁻¹ = F.X 5 ff := by
      rw [hc4_eq]
      have := F.mu_X'_conj_X (i := 12) (t := c4) (by decide) hc40 (j := 11) (dd⁻¹)
      norm_num [wtX] at this
      rw [this, show (21 : ℤ) = 5 + 16 by norm_num, F.X_add_sixteen]
      congr 1
      have hsc4 : F.sigma c4 = (f ^ 2 * F.sigma f)⁻¹ := by
        rw [hc4, map_inv₀, map_mul, F.sigma_sigma]
      rw [hsc4, hf, hdd, hff]
      simp only [map_mul, map_pow, F.sigma_sigma]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm4 hR4
    rwa [hconj] at this
  have h12 : s 12 = F.X' 12 c4 := by
    have h := hrec 4 (by norm_num)
    norm_num at h
    rw [h, h4, T.nu'_inv (i := 4) (u := F.X 4 f) (by norm_num : 3 ≤ 8)
      (F.X_mem 4 f) (F.X_ne_one 4 hf0),
      F.nu_X_even (j := 4) (t := f) (by decide) hf0]
    rw [show (4 : ℤ) + 8 = 12 by norm_num, ← hc4,
      F.X'_inv (j := 12) (by decide) c4]
  have h6 : s 6 = F.X' 6 hh := by
    have hm5 : T.mu 5 (F.X 5 ff) * T.mu 5 (F.X 5 ff) = 1 :=
      F.mu_X_mul_self 5 hff0
    have hR5 := hR 5 (by norm_num)
    norm_num at hR5
    rw [h5, h12] at hR5
    have hconj : T.mu 5 (F.X 5 ff) * F.X' 12 c4 * (T.mu 5 (F.X 5 ff))⁻¹ =
        F.X' 6 hh := by
      have := F.mu_X_odd_conj_X' (i := 5) (t := ff) (by decide) hff0 (j := 12) (by decide) c4
      norm_num [wtX'] at this
      rw [this]
      congr 1
      rw [hff, hhh, hc4, hf]
      simp only [map_mul, map_pow, F.sigma_sigma]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm5 hR5
    rwa [hconj] at this
  have h13 : s 13 = F.X 13 ff⁻¹ := by
    have h := hrec 5 (by norm_num)
    norm_num at h
    rw [h, h5, F.nu'_X_odd (j := 5) (t := ff) (by decide) hff0]
    norm_num
  have h7 : s 7 = F.X 7 (t * F.sigma u * u ^ 2) := by
    have hm6 : T.mu 6 (F.X' 6 hh) * T.mu 6 (F.X' 6 hh) = 1 :=
      F.mu_X'_mul_self (i := 6) (t := hh) (by decide) hhh0
    have hR6 := hR 6 (by norm_num)
    norm_num at hR6
    rw [h6, h13] at hR6
    have hconj : T.mu 6 (F.X' 6 hh) * F.X 13 ff⁻¹ * (T.mu 6 (F.X' 6 hh))⁻¹ =
        F.X 7 (t * F.sigma u * u ^ 2) := by
      have := F.mu_X'_conj_X (i := 6) (t := hh) (by decide) hhh0 (j := 13) (ff⁻¹)
      norm_num [wtX] at this
      rw [this]
      congr 1
      rw [hhh, hff]
      simp only [map_mul, map_pow, F.sigma_sigma]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm6 hR6
    rwa [hconj] at this
  have hC1 := hC 1 (by norm_num)
  norm_num at hC1
  rw [h1, h8, F.X_inv_odd (j := 1) (by decide) t] at hC1
  rw [show List.range' 2 6 = [2, 3, 4, 5, 6, 7] by decide] at hC1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hC1
  rw [h2, h3, h4, h5, h6, h7] at hC1
  calc ⁅F.X 1 t, F.X 8 u⁆
      = F.X 2 a * (F.X 3 dd * ((F.X 4 f)⁻¹ * (F.X 5 ff *
          (F.X' 6 hh * F.X 7 (t * F.sigma u * u ^ 2))))) := hC1
    _ = F.X 2 a * F.X 3 dd * (F.X 4 f)⁻¹ * F.X 5 ff * F.X' 6 hh *
          F.X 7 (t * F.sigma u * u ^ 2) := by group

theorem r7 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (1 + s) t, F.X (8 + s) u⁆ =
      F.X (2 + s) (t * u) * F.X (3 + s) (F.sigma t * t * F.sigma u * u ^ 2) *
        (F.X (4 + s) (F.sigma t * F.sigma u * u))⁻¹ *
        F.X (5 + s) (F.sigma t * t * F.sigma u ^ 2 * u ^ 2) *
        F.X' (6 + s) (F.sigma t * t * F.sigma u ^ 2 * u ^ 3) *
        F.X (7 + s) (t * F.sigma u * u ^ 2) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ k)) (F.comm_X1_X8 t u)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv,
    F.conj_rho_X, F.conj_rho_X'] at h
  rwa [show (1 : ℤ) + 2 * k = 1 + s by omega,
    show (2 : ℤ) + 2 * k = 2 + s by omega,
    show (3 : ℤ) + 2 * k = 3 + s by omega,
    show (4 : ℤ) + 2 * k = 4 + s by omega,
    show (5 : ℤ) + 2 * k = 5 + s by omega,
    show (6 : ℤ) + 2 * k = 6 + s by omega,
    show (7 : ℤ) + 2 * k = 7 + s by omega,
    show (8 : ℤ) + 2 * k = 8 + s by omega] at h

theorem comm_X1_X'8 (t u : F.K) :
    ⁅F.X 1 t, F.X' 8 u⁆ =
      F.X' 2 (F.sigma t * t * u) * F.X 3 (F.sigma t * t * F.sigma u) * F.X 4 (F.sigma t * u) *
        F.X 5 (F.sigma t * t * u ^ 2) * (F.X 6 (t * u))⁻¹ * F.X 7 (t * F.sigma u) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hst : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  have hsu : F.sigma u ≠ 0 := (map_ne_zero F.sigma).2 hu
  set cc : F.K := F.sigma t * t * u with hcc
  have hcc0 : cc ≠ 0 := by
    rw [hcc]
    exact mul_ne_zero (mul_ne_zero hst ht) hu
  set dd : F.K := F.sigma t * t * F.sigma u with hdd
  have hdd0 : dd ≠ 0 := by
    rw [hdd]
    exact mul_ne_zero (mul_ne_zero hst ht) hsu
  set ee : F.K := F.sigma t * u with hee
  have hee0 : ee ≠ 0 := by rw [hee]; exact mul_ne_zero hst hu
  set ff : F.K := F.sigma t * t * u ^ 2 with hff
  have hff0 : ff ≠ 0 := by
    rw [hff]
    exact mul_ne_zero (mul_ne_zero hst ht) (pow_ne_zero 2 hu)
  set gg : F.K := t * u with hgg
  have hgg0 : gg ≠ 0 := by rw [hgg]; exact mul_ne_zero ht hu
  obtain ⟨s, hs1, hs8, hmem, hrec, hC, hR⟩ :=
    T.lemma29 (by norm_num : 3 ≤ 8) (F.X_mem 1 t) (F.X_ne_one 1 ht)
      (T.Uprime_le 8 (F.X'_mem (j := 8) (by decide) u))
      (F.X'_ne_one (j := 8) (by decide) hu)
  have h1 : s 1 = F.X 1 t := by
    rw [hs1, F.X_inv_odd (j := 1) (by decide) t]
  have h8 : s 8 = F.X' 8 u := hs8
  have h2 : s 2 = F.X' 2 cc := by
    have hm1 : T.mu 1 (F.X 1 t) * T.mu 1 (F.X 1 t) = 1 :=
      F.mu_X_mul_self 1 ht
    have hR1 := hR 1 (by norm_num)
    norm_num at hR1
    rw [h1, h8] at hR1
    have hconj : T.mu 1 (F.X 1 t) * F.X' 8 u * (T.mu 1 (F.X 1 t))⁻¹ = F.X' 2 cc := by
      have := F.mu_X_odd_conj_X' (i := 1) (t := t) (by decide) ht (j := 8) (by decide) u
      norm_num [wtX'] at this
      simpa [hcc] using this
    have := eq_of_conj_eq hm1 hR1
    rwa [hconj] at this
  have h9 : s 9 = F.X 9 t⁻¹ := by
    have h := hrec 1 (by norm_num)
    norm_num at h
    rw [h, h1, F.nu'_X_odd (j := 1) (t := t) (by decide) ht]
    norm_num
  have h3 : s 3 = F.X 3 dd := by
    have hm2 : T.mu 2 (F.X' 2 cc) * T.mu 2 (F.X' 2 cc) = 1 :=
      F.mu_X'_mul_self (i := 2) (t := cc) (by decide) hcc0
    have hR2 := hR 2 (by norm_num)
    norm_num at hR2
    rw [h2, h9] at hR2
    have hconj : T.mu 2 (F.X' 2 cc) * F.X 9 t⁻¹ * (T.mu 2 (F.X' 2 cc))⁻¹ = F.X 3 dd := by
      have := F.mu_X'_conj_X (i := 2) (t := cc) (by decide) hcc0 (j := 9) (t⁻¹)
      norm_num [wtX] at this
      rw [this]
      congr 1
      rw [hcc, hdd]
      simp only [map_mul, map_pow, F.sigma_sigma]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm2 hR2
    rwa [hconj] at this
  have h10 : s 10 = F.X 10 (cc / F.sigma cc) := by
    have h := hrec 2 (by norm_num)
    norm_num at h
    rw [h, h2, F.nu'_X' (j := 2) (t := cc) (by decide) hcc0]
    norm_num
  have h4 : s 4 = F.X 4 ee := by
    have hm3 : T.mu 3 (F.X 3 dd) * T.mu 3 (F.X 3 dd) = 1 :=
      F.mu_X_mul_self 3 hdd0
    have hR3 := hR 3 (by norm_num)
    norm_num at hR3
    rw [h3, h10] at hR3
    have hconj : T.mu 3 (F.X 3 dd) * F.X 10 (cc / F.sigma cc) *
        (T.mu 3 (F.X 3 dd))⁻¹ = F.X 4 ee := by
      have := F.mu_X_odd_conj_X (i := 3) (t := dd) (by decide) hdd0 (j := 10)
        (cc / F.sigma cc)
      norm_num [wtX] at this
      rw [this]
      congr 1
      rw [hdd, hee, hcc]
      simp only [map_mul, map_pow, F.sigma_sigma]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm3 hR3
    rwa [hconj] at this
  have h11 : s 11 = F.X 11 dd⁻¹ := by
    have h := hrec 3 (by norm_num)
    norm_num at h
    rw [h, h3, F.nu'_X_odd (j := 3) (t := dd) (by decide) hdd0]
    norm_num
  set c : F.K := (F.sigma ee * ee)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero ((map_ne_zero F.sigma).2 hee0) hee0)
  have h5 : s 5 = F.X 5 ff := by
    have hm4 : T.mu 4 (F.X 4 ee) * T.mu 4 (F.X 4 ee) = 1 :=
      F.mu_X_mul_self 4 hee0
    have hR4 := hR 4 (by norm_num)
    norm_num at hR4
    rw [h4, h11] at hR4
    have hc_eq : T.mu 4 (F.X 4 ee) = T.mu 12 (F.X' 12 c) := by
      rw [F.mu_X_even (i := 4) (t := ee) (by decide) hee0, hc]
      norm_num
    have hconj : T.mu 4 (F.X 4 ee) * F.X 11 dd⁻¹ * (T.mu 4 (F.X 4 ee))⁻¹ = F.X 5 ff := by
      rw [hc_eq]
      have := F.mu_X'_conj_X (i := 12) (t := c) (by decide) hc0 (j := 11) (dd⁻¹)
      norm_num [wtX] at this
      rw [this, show (21 : ℤ) = 5 + 16 by norm_num, F.X_add_sixteen]
      congr 1
      have hsc : F.sigma c = (ee ^ 2 * F.sigma ee)⁻¹ := by
        rw [hc, map_inv₀, map_mul, F.sigma_sigma]
      rw [hsc, hee, hdd, hff]
      simp only [map_mul, map_pow, F.sigma_sigma]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm4 hR4
    rwa [hconj] at this
  have h12 : s 12 = (F.X 12 ee⁻¹)⁻¹ := by
    have h := hrec 4 (by norm_num)
    norm_num at h
    rw [h, h4, F.nu'_X_even (j := 4) (t := ee) (by decide) hee0]
    norm_num
  have h6 : s 6 = (F.X 6 gg)⁻¹ := by
    have hm5 : T.mu 5 (F.X 5 ff) * T.mu 5 (F.X 5 ff) = 1 :=
      F.mu_X_mul_self 5 hff0
    have hR5 := hR 5 (by norm_num)
    norm_num at hR5
    rw [h5, h12] at hR5
    have hconj : T.mu 5 (F.X 5 ff) * (F.X 12 ee⁻¹)⁻¹ * (T.mu 5 (F.X 5 ff))⁻¹ =
        (F.X 6 gg)⁻¹ := by
      have hg : T.mu 5 (F.X 5 ff) * F.X 12 ee⁻¹ * (T.mu 5 (F.X 5 ff))⁻¹ =
          F.X 6 (ff * ee⁻¹) := by
        have := F.mu_X_odd_conj_X (i := 5) (t := ff) (by decide) hff0 (j := 12) (ee⁻¹)
        norm_num [wtX] at this
        simpa using this
      calc T.mu 5 (F.X 5 ff) * (F.X 12 ee⁻¹)⁻¹ * (T.mu 5 (F.X 5 ff))⁻¹
          = (T.mu 5 (F.X 5 ff) * F.X 12 ee⁻¹ * (T.mu 5 (F.X 5 ff))⁻¹)⁻¹ := by group
        _ = (F.X 6 (ff * ee⁻¹))⁻¹ := by rw [hg]
        _ = (F.X 6 gg)⁻¹ := by
            congr 1
            rw [hff, hee, hgg]
            field_simp [ht, hu]
    have := eq_of_conj_eq hm5 hR5
    rwa [hconj] at this
  have h13 : s 13 = F.X 13 ff⁻¹ := by
    have h := hrec 5 (by norm_num)
    norm_num at h
    rw [h, h5, F.nu'_X_odd (j := 5) (t := ff) (by decide) hff0]
    norm_num
  set c2 : F.K := (F.sigma gg * gg)⁻¹ with hc2
  have hc20 : c2 ≠ 0 := inv_ne_zero (mul_ne_zero ((map_ne_zero F.sigma).2 hgg0) hgg0)
  have h7 : s 7 = F.X 7 (t * F.sigma u) := by
    have hm6 : T.mu 6 (F.X 6 gg) * T.mu 6 (F.X 6 gg) = 1 :=
      F.mu_X_mul_self 6 hgg0
    have hm6inv : T.mu 6 ((F.X 6 gg)⁻¹) = T.mu 6 (F.X 6 gg) := by
      rw [T.mu_inv (i := 6) (u := F.X 6 gg) (by norm_num : 3 ≤ 8)
        (F.X_mem 6 gg) (F.X_ne_one 6 hgg0)]
      exact inv_eq_of_mul_eq_one_right hm6
    have hR6 := hR 6 (by norm_num)
    norm_num at hR6
    rw [h6, h13, hm6inv] at hR6
    have hconj : T.mu 6 (F.X 6 gg) * F.X 13 ff⁻¹ * (T.mu 6 (F.X 6 gg))⁻¹ =
        F.X 7 (t * F.sigma u) := by
      have hc2_eq : T.mu 6 (F.X 6 gg) = T.mu 14 (F.X' 14 c2) := by
        rw [F.mu_X_even (i := 6) (t := gg) (by decide) hgg0, hc2]
        norm_num
      rw [hc2_eq]
      have := F.mu_X'_conj_X (i := 14) (t := c2) (by decide) hc20 (j := 13) (ff⁻¹)
      norm_num [wtX] at this
      rw [this, show (23 : ℤ) = 7 + 16 by norm_num, F.X_add_sixteen]
      congr 1
      have hsc2 : F.sigma c2 = (gg ^ 2 * F.sigma gg)⁻¹ := by
        rw [hc2, map_inv₀, map_mul, F.sigma_sigma]
      rw [hsc2, hgg, hff]
      simp only [map_mul, map_pow, F.sigma_sigma]
      field_simp [ht, hu, hst, hsu]
    have := eq_of_conj_eq hm6 hR6
    rwa [hconj] at this
  have hC1 := hC 1 (by norm_num)
  norm_num at hC1
  rw [h1, h8, F.X_inv_odd (j := 1) (by decide) t] at hC1
  rw [show List.range' 2 6 = [2, 3, 4, 5, 6, 7] by decide] at hC1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hC1
  rw [h2, h3, h4, h5, h6, h7] at hC1
  calc ⁅F.X 1 t, F.X' 8 u⁆
      = F.X' 2 cc * (F.X 3 dd * (F.X 4 ee * (F.X 5 ff *
          ((F.X 6 gg)⁻¹ * F.X 7 (t * F.sigma u))))) := hC1
    _ = F.X' 2 cc * F.X 3 dd * F.X 4 ee * F.X 5 ff * (F.X 6 gg)⁻¹ *
          F.X 7 (t * F.sigma u) := by group

theorem r6 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (1 + s) t, F.X' (8 + s) u⁆ =
      F.X' (2 + s) (F.sigma t * t * u) * F.X (3 + s) (F.sigma t * t * F.sigma u) *
        F.X (4 + s) (F.sigma t * u) * F.X (5 + s) (F.sigma t * t * u ^ 2) *
        (F.X (6 + s) (t * u))⁻¹ * F.X (7 + s) (t * F.sigma u) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ k)) (F.comm_X1_X'8 t u)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv,
    F.conj_rho_X, F.conj_rho_X'] at h
  rwa [show (1 : ℤ) + 2 * k = 1 + s by omega,
    show (2 : ℤ) + 2 * k = 2 + s by omega,
    show (3 : ℤ) + 2 * k = 3 + s by omega,
    show (4 : ℤ) + 2 * k = 4 + s by omega,
    show (5 : ℤ) + 2 * k = 5 + s by omega,
    show (6 : ℤ) + 2 * k = 6 + s by omega,
    show (7 : ℤ) + 2 * k = 7 + s by omega,
    show (8 : ℤ) + 2 * k = 8 + s by omega] at h

end OctFrame

end CFSG.GH74.Tits83
