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

theorem comm_X0_X3 (t u : F.K) : ⁅F.X 0 t, F.X 3 u⁆ = F.X' 2 (t * u) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hst : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  set c : F.K := (F.sigma t * t)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero hst ht)
  have hsc : F.sigma c = (t ^ 2 * F.sigma t)⁻¹ := by
    rw [hc, map_inv₀, map_mul, F.sigma_sigma]
  have hct : c / F.sigma c = t := by
    rw [hsc, hc]
    field_simp
  have hv : F.X' 8 c ∈ T.Uprime 8 := F.X'_mem (by decide) c
  have hv1 : F.X' 8 c ≠ 1 := F.X'_ne_one (by decide) hc0
  have h := T.lemma34_i F.hT (F.X_mem 3 u) (F.X_ne_one 3 hu) hv hv1
  rw [F.nu_X' (by decide) hc0, show (8 : ℤ) + 8 = 0 + 16 by norm_num, F.X_add_sixteen, hct,
    F.X_inv_odd (j := 3) (by decide)] at h
  have hm3 : (T.mu 3 (F.X 3 u))⁻¹ = T.mu 3 (F.X 3 u) :=
    inv_eq_of_mul_eq_one_right (F.mu_X_mul_self 3 hu)
  have h1 : (T.mu 3 (F.X 3 u))⁻¹ * F.X' 8 c * T.mu 3 (F.X 3 u) = F.X' 6 (u * c) := by
    have := F.mu_X_odd_conj_X' (i := 3) (by decide) hu (j := 8) (by decide) c
    norm_num [wtX'] at this
    rw [hm3] at this ⊢
    exact this
  have hsc0 : F.sigma c ≠ 0 := (map_ne_zero F.sigma).2 hc0
  have h2 : T.mu 8 (F.X' 8 c) * F.X' 6 (u * c) * (T.mu 8 (F.X' 8 c))⁻¹ = F.X' 2 (t * u) := by
    have := F.mu_X'_conj_X' (i := 8) (by decide) hc0 (j := 6) (by decide) (u * c)
    norm_num [wtX'] at this
    rw [this, show (18 : ℤ) = 2 + 16 by norm_num, F.X'_add_sixteen]
    congr 1
    rw [← hct]
    field_simp
  rw [h1, h2] at h
  have hg : F.X 0 t * F.X 0 t ∈ T.Uprime 0 := T.lemma316_iii F.hT (by decide) (F.X_mem 0 t)
  have hgc : F.X 0 t * F.X 0 t * F.X 3 u = F.X 3 u * (F.X 0 t * F.X 0 t) :=
    T.Uprime_comm (j := 0) (k := 3) (by norm_num) (by norm_num) hg (F.X_mem 3 u)
  have key : ⁅F.X 0 t, F.X 3 u⁆ = ⁅(F.X 0 t)⁻¹, F.X 3 u⁆ := by
    have e : F.X 0 t = (F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t) := by group
    conv_lhs => rw [e]
    simp only [commutatorElement_def]
    calc (F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t) * F.X 3 u * ((F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t))⁻¹ *
          (F.X 3 u)⁻¹
        = (F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t * F.X 3 u) * (F.X 0 t * F.X 0 t)⁻¹ * (F.X 0 t)⁻¹⁻¹ *
          (F.X 3 u)⁻¹ := by group
      _ = (F.X 0 t)⁻¹ * F.X 3 u * (F.X 0 t)⁻¹⁻¹ * (F.X 3 u)⁻¹ := by rw [hgc]; group
  rw [key, h]
theorem r9 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (2 + s) t, F.X (5 + s) u⁆ = F.X' (4 + s) (t * u) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ (k + 1))) (F.comm_X0_X3 t u)
  simp only [map_commutatorElement, MulAut.conj_apply, F.conj_rho_X, F.conj_rho_X'] at h
  rwa [show (0 : ℤ) + 2 * (k + 1) = 2 + s by omega,
    show (3 : ℤ) + 2 * (k + 1) = 5 + s by omega,
    show (2 : ℤ) + 2 * (k + 1) = 4 + s by omega] at h
theorem r2 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (1 + s) t, F.X (4 + s) u⁆ = F.X' (2 + s) (t * u) := by
  have h0 := congrArg (MulAut.conj F.a) (F.comm_X0_X3 u t)
  simp only [map_commutatorElement, MulAut.conj_apply, F.conj_a_X,
    F.conj_a_X' (by decide : Even (2 : ℤ))] at h0
  have h1 : ⁅F.X 7 t, F.X 10 u⁆ = F.X' 8 (t * u) := by
    rw [← commutatorElement_inv]
    norm_num at h0
    rw [h0, F.X'_inv (by decide), mul_comm]
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ (k - 3))) h1
  simp only [map_commutatorElement, MulAut.conj_apply, F.conj_rho_X, F.conj_rho_X'] at h
  rwa [show (7 : ℤ) + 2 * (k - 3) = 1 + s by omega,
    show (10 : ℤ) + 2 * (k - 3) = 4 + s by omega,
    show (8 : ℤ) + 2 * (k - 3) = 2 + s by omega] at h
theorem comm_X0_X5 (t u : F.K) :
    ⁅F.X 0 t, F.X 5 u⁆ = F.X' 2 (F.sigma t * t * u) * F.X 3 (F.sigma t * u) *
      F.X' 4 (t * F.sigma u) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hst : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  have hsu : F.sigma u ≠ 0 := (map_ne_zero F.sigma).2 hu
  set c : F.K := (F.sigma t * t)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero hst ht)
  have hsc : F.sigma c = (t ^ 2 * F.sigma t)⁻¹ := by
    rw [hc, map_inv₀, map_mul, F.sigma_sigma]
  have hct : c / F.sigma c = t := by
    rw [hsc, hc]
    field_simp
  set d : F.K := F.sigma t * u with hd
  have hd0 : d ≠ 0 := mul_ne_zero hst hu
  set e : F.K := F.sigma t * t * u with he
  have he0 : e ≠ 0 := mul_ne_zero (mul_ne_zero hst ht) hu
  have hv : F.X' 8 c ∈ T.Uprime 8 := F.X'_mem (by decide) c
  have hv1 : F.X' 8 c ≠ 1 := F.X'_ne_one (by decide) hc0
  have hm8 : (T.mu 8 (F.X' 8 c))⁻¹ = T.mu 8 (F.X' 8 c) :=
    inv_eq_of_mul_eq_one_right (F.mu_X'_mul_self (by decide) hc0)
  have hcomm : ⁅F.X 3 d, F.X' 8 c⁆ = F.X' 6 (d * c) := by
    have := F.r3 2 (by decide) d c
    norm_num at this
    exact this
  have hu' : F.X' 2 e = (T.mu 8 (F.X' 8 c))⁻¹ * ⁅F.X 3 d, F.X' 8 c⁆ * T.mu 8 (F.X' 8 c) := by
    rw [hcomm, hm8]
    have := F.mu_X'_conj_X' (i := 8) (by decide) hc0 (j := 6) (by decide) (d * c)
    norm_num [wtX'] at this
    rw [hm8] at this
    rw [this, show (18 : ℤ) = 2 + 16 by norm_num, F.X'_add_sixteen]
    congr 1
    rw [he, hd, hc]
    have hsc' : F.sigma (F.sigma t * t)⁻¹ = (t ^ 2 * F.sigma t)⁻¹ := by
      rw [map_inv₀, map_mul, F.sigma_sigma]
    rw [hsc']
    field_simp
  have h := T.lemma38_iii F.hT hv hv1 (F.X_mem 3 d) (F.X_ne_one 3 hd0) hu'
  rw [F.nu_X' (by decide) hc0, inv_inv, show (8 : ℤ) + 8 = 0 + 16 by norm_num, F.X_add_sixteen,
    hct] at h
  have h5 : T.mu 8 (F.X' 8 c) * F.X 3 d * (T.mu 8 (F.X' 8 c))⁻¹ = F.X 5 u := by
    have := F.mu_X'_conj_X (i := 8) (by decide) hc0 (j := 3) d
    norm_num [wtX] at this
    rw [this, show (21 : ℤ) = 5 + 16 by norm_num, F.X_add_sixteen]
    congr 1
    rw [hsc, hc, hd]
    field_simp
  have h4 : T.mu 2 (F.X' 2 e) * (F.X' 8 c)⁻¹ * (T.mu 2 (F.X' 2 e))⁻¹ =
      F.X' 4 (t * F.sigma u) := by
    rw [F.X'_inv (by decide)]
    have := F.mu_X'_conj_X' (i := 2) (by decide) he0 (j := 8) (by decide) c
    norm_num [wtX'] at this
    rw [this]
    congr 1
    have hse : F.sigma e = t ^ 2 * F.sigma t * F.sigma u := by
      rw [he, map_mul, map_mul, F.sigma_sigma]
    rw [hse, he, hc]
    field_simp
  rw [h5, h4] at h
  exact h
theorem r11 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (2 + s) t, F.X (7 + s) u⁆ =
      F.X' (4 + s) (F.sigma t * t * u) * F.X (5 + s) (F.sigma t * u) *
        F.X' (6 + s) (t * F.sigma u) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ (k + 1))) (F.comm_X0_X5 t u)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv,
    F.conj_rho_X, F.conj_rho_X'] at h
  rwa [show (0 : ℤ) + 2 * (k + 1) = 2 + s by omega,
    show (5 : ℤ) + 2 * (k + 1) = 7 + s by omega,
    show (2 : ℤ) + 2 * (k + 1) = 4 + s by omega,
    show (3 : ℤ) + 2 * (k + 1) = 5 + s by omega,
    show (4 : ℤ) + 2 * (k + 1) = 6 + s by omega] at h
theorem r4 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (1 + s) t, F.X (6 + s) u⁆ =
      F.X' (2 + s) (F.sigma t * u) * F.X (3 + s) (t * F.sigma u) *
        F.X' (4 + s) (t * F.sigma u * u) := by
  have h0 := congrArg (MulAut.conj F.a) (F.comm_X0_X5 u t)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv,
    F.conj_a_X, F.conj_a_X' (by decide : Even (2 : ℤ)),
    F.conj_a_X' (by decide : Even (4 : ℤ))] at h0
  norm_num at h0
  have h1 : ⁅F.X 5 t, F.X 10 u⁆ =
      F.X' 6 (u * F.sigma t) * F.X 7 (F.sigma u * t) *
        F.X' 8 (F.sigma u * u * t) := by
    rw [← commutatorElement_inv, h0]
    simp only [mul_inv_rev, F.X'_inv (j := 6) (by decide),
      F.X_inv_odd (j := 7) (by decide), F.X'_inv (j := 8) (by decide)]
    group
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ (k - 2))) h1
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv,
    F.conj_rho_X, F.conj_rho_X'] at h
  rw [show (5 : ℤ) + 2 * (k - 2) = 1 + s by omega,
    show (10 : ℤ) + 2 * (k - 2) = 6 + s by omega,
    show (6 : ℤ) + 2 * (k - 2) = 2 + s by omega,
    show (7 : ℤ) + 2 * (k - 2) = 3 + s by omega,
    show (8 : ℤ) + 2 * (k - 2) = 4 + s by omega] at h
  rw [h]
  congr 1 <;> ring_nf
private theorem conj_X1_X6 (y : F.K) :
    F.X 1 1 * F.X 6 y * (F.X 1 1)⁻¹ =
      F.X' 2 y * F.X 3 (F.sigma y) * F.X' 4 (F.sigma y * y) * F.X 6 y := by
  have h := F.r4 0 (by decide : Even (0 : ℤ)) 1 y
  simp only [add_zero, mul_one, map_one, one_mul] at h
  have h' : F.X 1 1 * F.X 6 y * (F.X 1 1)⁻¹ * (F.X 6 y)⁻¹ =
      F.X' 2 y * F.X 3 (F.sigma y) * F.X' 4 (F.sigma y * y) := by
    simpa [commutatorElement_def] using h
  calc
    F.X 1 1 * F.X 6 y * (F.X 1 1)⁻¹
        = (F.X 1 1 * F.X 6 y * (F.X 1 1)⁻¹ * (F.X 6 y)⁻¹) * F.X 6 y := by group
    _ = F.X' 2 y * F.X 3 (F.sigma y) * F.X' 4 (F.sigma y * y) * F.X 6 y := by rw [h']

private theorem conj_X1_Xp6 (z : F.K) :
    F.X 1 1 * F.X' 6 z * (F.X 1 1)⁻¹ = F.X' 4 z * F.X' 6 z := by
  have h := F.r3 0 (by decide : Even (0 : ℤ)) 1 z
  simp only [add_zero, mul_one, map_one, one_mul] at h
  have h' : F.X 1 1 * F.X' 6 z * (F.X 1 1)⁻¹ * (F.X' 6 z)⁻¹ = F.X' 4 z := by
    simpa [commutatorElement_def] using h
  calc
    F.X 1 1 * F.X' 6 z * (F.X 1 1)⁻¹
        = (F.X 1 1 * F.X' 6 z * (F.X 1 1)⁻¹ * (F.X' 6 z)⁻¹) * F.X' 6 z := by group
    _ = F.X' 4 z * F.X' 6 z := by rw [h']

private theorem collect_X6 (x x' : F.K) :
    (F.X' 2 x * F.X 3 (F.sigma x) * F.X' 4 (F.sigma x * x) * F.X 6 x) *
        (F.X' 2 x' * F.X 3 (F.sigma x') * F.X' 4 (F.sigma x' * x') * F.X 6 x') =
      F.X' 2 (x + x') * F.X 3 (F.sigma x + F.sigma x') *
        F.X' 4 (F.sigma x * x + x * F.sigma x' + F.sigma x' * x') * F.X 6 x * F.X 6 x' := by
  set a : G := F.X' 2 x
  set b : G := F.X 3 (F.sigma x)
  set c : G := F.X' 4 (F.sigma x * x)
  set d : G := F.X 6 x
  set e : G := F.X' 2 x'
  set f : G := F.X 3 (F.sigma x')
  set g : G := F.X' 4 (F.sigma x' * x')
  set h : G := F.X 6 x'
  set A : G := F.X' 2 (x + x')
  set B : G := F.X 3 (F.sigma x + F.sigma x')
  set C : G := F.X' 4 (F.sigma x * x + x * F.sigma x' + F.sigma x' * x')
  set p : G := F.X' 4 (x * F.sigma x')
  set q : G := F.X' 4 (F.sigma x * x + x * F.sigma x')
  have hde : d * e = e * d := by
    change F.X 6 x * F.X' 2 x' = F.X' 2 x' * F.X 6 x
    exact (F.c2'6 0 (by decide : Even (0 : ℤ)) x' x).symm
  have hdf : d * f = p * f * d := by
    change F.X 6 x * F.X 3 (F.sigma x') =
      F.X' 4 (x * F.sigma x') * F.X 3 (F.sigma x') * F.X 6 x
    have hcomm : ⁅F.X 6 x, F.X 3 (F.sigma x')⁆ = F.X' 4 (x * F.sigma x') := by
      have hr := F.r2 2 (by decide : Even (2 : ℤ)) (F.sigma x') x
      norm_num at hr
      rw [← commutatorElement_inv, hr, F.X'_inv (j := 4) (by decide), mul_comm (F.sigma x') x]
    calc
      F.X 6 x * F.X 3 (F.sigma x') =
          (F.X 6 x * F.X 3 (F.sigma x') * (F.X 6 x)⁻¹ *
            (F.X 3 (F.sigma x'))⁻¹) * F.X 3 (F.sigma x') * F.X 6 x := by group
      _ = F.X' 4 (x * F.sigma x') * F.X 3 (F.sigma x') * F.X 6 x := by
        rw [show F.X 6 x * F.X 3 (F.sigma x') * (F.X 6 x)⁻¹ *
            (F.X 3 (F.sigma x'))⁻¹ = ⁅F.X 6 x, F.X 3 (F.sigma x')⁆ from rfl, hcomm]
  have hdg : d * g = g * d := by
    change F.X 6 x * F.X' 4 (F.sigma x' * x') =
      F.X' 4 (F.sigma x' * x') * F.X 6 x
    exact (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num)
      (F.X'_mem (by decide : Even (4 : ℤ)) (F.sigma x' * x'))
      (F.X_mem 6 x)).symm
  have hce : c * e = e * c := by
    change F.X' 4 (F.sigma x * x) * F.X' 2 x' =
      F.X' 2 x' * F.X' 4 (F.sigma x * x)
    exact T.Uprime_comm (j := 4) (k := 2) (by norm_num) (by norm_num)
      (F.X'_mem (by decide : Even (4 : ℤ)) (F.sigma x * x))
      (T.Uprime_le 2 (F.X'_mem (by decide : Even (2 : ℤ)) x'))
  have hbe : b * e = e * b := by
    change F.X 3 (F.sigma x) * F.X' 2 x' = F.X' 2 x' * F.X 3 (F.sigma x)
    exact (T.Uprime_comm (j := 2) (k := 3) (by norm_num) (by norm_num)
      (F.X'_mem (by decide : Even (2 : ℤ)) x')
      (F.X_mem 3 (F.sigma x))).symm
  have hae : a * e = A := by
    change F.X' 2 x * F.X' 2 x' = F.X' 2 (x + x')
    exact (F.X'_add (by decide : Even (2 : ℤ)) x x').symm
  have hcp : c * p = q := by
    change F.X' 4 (F.sigma x * x) * F.X' 4 (x * F.sigma x') =
      F.X' 4 (F.sigma x * x + x * F.sigma x')
    exact (F.X'_add (by decide : Even (4 : ℤ)) (F.sigma x * x) (x * F.sigma x')).symm
  have hqf : q * f = f * q := by
    change F.X' 4 (F.sigma x * x + x * F.sigma x') * F.X 3 (F.sigma x') =
      F.X 3 (F.sigma x') * F.X' 4 (F.sigma x * x + x * F.sigma x')
    exact T.Uprime_comm (j := 4) (k := 3) (by norm_num) (by norm_num)
      (F.X'_mem (by decide : Even (4 : ℤ)) (F.sigma x * x + x * F.sigma x'))
      (F.X_mem 3 (F.sigma x'))
  have hqg : q * g = C := by
    change F.X' 4 (F.sigma x * x + x * F.sigma x') * F.X' 4 (F.sigma x' * x') =
      F.X' 4 (F.sigma x * x + x * F.sigma x' + F.sigma x' * x')
    exact (F.X'_add (by decide : Even (4 : ℤ)) (F.sigma x * x + x * F.sigma x')
      (F.sigma x' * x')).symm
  have hbf : b * f = B := by
    change F.X 3 (F.sigma x) * F.X 3 (F.sigma x') = F.X 3 (F.sigma x + F.sigma x')
    exact (F.X_add_odd (j := 3) (by decide : Odd (3 : ℤ)) (F.sigma x) (F.sigma x')).symm
  calc
    (a * b * c * d) * (e * f * g * h) = a * b * c * (d * e) * f * g * h := by group
    _ = a * b * c * (e * d) * f * g * h := by rw [hde]
    _ = a * b * c * e * (d * f) * g * h := by group
    _ = a * b * c * e * (p * f * d) * g * h := by rw [hdf]
    _ = a * b * c * e * p * f * (d * g) * h := by group
    _ = a * b * c * e * p * f * (g * d) * h := by rw [hdg]
    _ = a * b * (c * e) * p * f * g * d * h := by group
    _ = a * b * (e * c) * p * f * g * d * h := by rw [hce]
    _ = a * (b * e) * c * p * f * g * d * h := by group
    _ = a * (e * b) * c * p * f * g * d * h := by rw [hbe]
    _ = (a * e) * b * c * p * f * g * d * h := by group
    _ = A * b * c * p * f * g * d * h := by rw [hae]
    _ = A * b * (c * p) * f * g * d * h := by group
    _ = A * b * q * f * g * d * h := by rw [hcp]
    _ = A * b * (q * f) * g * d * h := by group
    _ = A * b * (f * q) * g * d * h := by rw [hqf]
    _ = A * b * f * (q * g) * d * h := by group
    _ = A * b * f * C * d * h := by rw [hqg]
    _ = A * (b * f) * C * d * h := by group
    _ = A * B * C * d * h := by rw [hbf]

private theorem collect_X6p (x z : F.K) :
    (F.X' 2 x * F.X 3 (F.sigma x) * F.X' 4 (F.sigma x * x) * F.X 6 x) *
        (F.X' 4 z * F.X' 6 z) =
      F.X' 2 x * F.X 3 (F.sigma x) * F.X' 4 (F.sigma x * x + z) * F.X 6 x * F.X' 6 z := by
  set a : G := F.X' 2 x
  set b : G := F.X 3 (F.sigma x)
  set c : G := F.X' 4 (F.sigma x * x)
  set d : G := F.X 6 x
  set g : G := F.X' 4 z
  set h : G := F.X' 6 z
  set C : G := F.X' 4 (F.sigma x * x + z)
  have hdg : d * g = g * d := by
    change F.X 6 x * F.X' 4 z = F.X' 4 z * F.X 6 x
    exact (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num)
      (F.X'_mem (by decide : Even (4 : ℤ)) z) (F.X_mem 6 x)).symm
  have hcg : c * g = C := by
    change F.X' 4 (F.sigma x * x) * F.X' 4 z = F.X' 4 (F.sigma x * x + z)
    exact (F.X'_add (by decide : Even (4 : ℤ)) (F.sigma x * x) z).symm
  calc
    (a * b * c * d) * (g * h) = a * b * c * (d * g) * h := by group
    _ = a * b * c * (g * d) * h := by rw [hdg]
    _ = a * b * (c * g) * d * h := by group
    _ = a * b * C * d * h := by rw [hcg]

theorem X_mul_even_six (t u : F.K) :
    F.X 6 t * F.X 6 u = F.X 6 (t + u) * F.X' 6 (u * F.sigma t) := by
  obtain ⟨⟨x'', z⟩, hxz⟩ := (F.bij_even_X (j := 6) (by decide : Even (6 : ℤ))).2
    ⟨F.X 6 t * F.X 6 u, (T.U 6).mul_mem (F.X_mem 6 t) (F.X_mem 6 u)⟩
  have hP : F.X 6 t * F.X 6 u = F.X 6 x'' * F.X' 6 z := by
    have := congrArg Subtype.val hxz
    simpa using this.symm
  have hL : F.X 1 1 * (F.X 6 t * F.X 6 u) * (F.X 1 1)⁻¹ =
      F.X' 2 (t + u) * F.X 3 (F.sigma t + F.sigma u) *
        F.X' 4 (F.sigma t * t + t * F.sigma u + F.sigma u * u) *
        F.X 6 t * F.X 6 u := by
    rw [show F.X 1 1 * (F.X 6 t * F.X 6 u) * (F.X 1 1)⁻¹ =
        (F.X 1 1 * F.X 6 t * (F.X 1 1)⁻¹) *
          (F.X 1 1 * F.X 6 u * (F.X 1 1)⁻¹) by group,
      conj_X1_X6 F t, conj_X1_X6 F u, collect_X6 F t u]
  have hR : F.X 1 1 * (F.X 6 x'' * F.X' 6 z) * (F.X 1 1)⁻¹ =
      F.X' 2 x'' * F.X 3 (F.sigma x'') * F.X' 4 (F.sigma x'' * x'' + z) *
        F.X 6 x'' * F.X' 6 z := by
    rw [show F.X 1 1 * (F.X 6 x'' * F.X' 6 z) * (F.X 1 1)⁻¹ =
        (F.X 1 1 * F.X 6 x'' * (F.X 1 1)⁻¹) *
          (F.X 1 1 * F.X' 6 z * (F.X 1 1)⁻¹) by group,
      conj_X1_X6 F x'', conj_X1_Xp6 F z, collect_X6p F x'' z]
  have hEq : F.X 1 1 * (F.X 6 t * F.X 6 u) * (F.X 1 1)⁻¹ =
      F.X 1 1 * (F.X 6 x'' * F.X' 6 z) * (F.X 1 1)⁻¹ := by rw [hP]
  rw [hL, hR] at hEq
  have hEq2 : F.X' 2 (t + u) *
        (F.X 3 (F.sigma t + F.sigma u) *
          F.X' 4 (F.sigma t * t + t * F.sigma u + F.sigma u * u) *
          F.X 6 t * F.X 6 u) =
      F.X' 2 x'' *
        (F.X 3 (F.sigma x'') * F.X' 4 (F.sigma x'' * x'' + z) *
          F.X 6 x'' * F.X' 6 z) := by
    simpa only [mul_assoc] using hEq
  have hA1mem : F.X' 2 (t + u) ∈ win T.U 2 2 := by
    rw [T.win_self]
    exact T.Uprime_le 2 (F.X'_mem (by decide : Even (2 : ℤ)) (t + u))
  have hA2mem : F.X' 2 x'' ∈ win T.U 2 2 := by
    rw [T.win_self]
    exact T.Uprime_le 2 (F.X'_mem (by decide : Even (2 : ℤ)) x'')
  have hS1mem : F.X 3 (F.sigma t + F.sigma u) *
        F.X' 4 (F.sigma t * t + t * F.sigma u + F.sigma u * u) *
        F.X 6 t * F.X 6 u ∈ win T.U 3 6 := by
    exact (win T.U 3 6).mul_mem
      ((win T.U 3 6).mul_mem
        ((win T.U 3 6).mul_mem
          (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 3 _))
          (T.U_le_win (by norm_num) (by norm_num)
            (T.Uprime_le 4 (F.X'_mem (by decide : Even (4 : ℤ)) _))))
        (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 t)))
      (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 u))
  have hS2mem : F.X 3 (F.sigma x'') *
        F.X' 4 (F.sigma x'' * x'' + z) * F.X 6 x'' * F.X' 6 z ∈ win T.U 3 6 := by
    exact (win T.U 3 6).mul_mem
      ((win T.U 3 6).mul_mem
        ((win T.U 3 6).mul_mem
          (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 3 _))
          (T.U_le_win (by norm_num) (by norm_num)
            (T.Uprime_le 4 (F.X'_mem (by decide : Even (4 : ℤ)) _))))
        (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 x'')))
      (T.U_le_win (by norm_num) (by norm_num)
        (T.Uprime_le 6 (F.X'_mem (by decide : Even (6 : ℤ)) z)))
  have hfirst := T.eq_of_mul_eq_mul (a := 2) (c := 2) (b := 6)
    (by norm_num) (by norm_num) (by norm_num) hA1mem hA2mem hS1mem hS2mem hEq2
  have hx'' : x'' = t + u := ((F.X'_injective (j := 2) (by decide : Even (2 : ℤ))) hfirst.1).symm
  subst x''
  have hB1mem : F.X' 2 (t + u) * F.X 3 (F.sigma t + F.sigma u) ∈ win T.U 2 3 := by
    exact (win T.U 2 3).mul_mem
      (T.U_le_win (by norm_num) (by norm_num)
        (T.Uprime_le 2 (F.X'_mem (by decide : Even (2 : ℤ)) (t + u))))
      (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 3 _))
  have hB2mem : F.X' 2 (t + u) * F.X 3 (F.sigma (t + u)) ∈ win T.U 2 3 := by
    exact (win T.U 2 3).mul_mem
      (T.U_le_win (by norm_num) (by norm_num)
        (T.Uprime_le 2 (F.X'_mem (by decide : Even (2 : ℤ)) (t + u))))
      (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 3 _))
  have hT1mem : F.X' 4 (F.sigma t * t + t * F.sigma u + F.sigma u * u) *
        F.X 6 t * F.X 6 u ∈ win T.U 4 6 := by
    exact (win T.U 4 6).mul_mem
      ((win T.U 4 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num)
          (T.Uprime_le 4 (F.X'_mem (by decide : Even (4 : ℤ)) _)))
        (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 t)))
      (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 u))
  have hT2mem : F.X' 4 (F.sigma (t + u) * (t + u) + z) *
        F.X 6 (t + u) * F.X' 6 z ∈ win T.U 4 6 := by
    exact (win T.U 4 6).mul_mem
      ((win T.U 4 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num)
          (T.Uprime_le 4 (F.X'_mem (by decide : Even (4 : ℤ)) _)))
        (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 (t + u))))
      (T.U_le_win (by norm_num) (by norm_num)
        (T.Uprime_le 6 (F.X'_mem (by decide : Even (6 : ℤ)) z)))
  have hEq3 : F.X' 2 (t + u) * F.X 3 (F.sigma t + F.sigma u) *
        (F.X' 4 (F.sigma t * t + t * F.sigma u + F.sigma u * u) *
          F.X 6 t * F.X 6 u) =
      F.X' 2 (t + u) * F.X 3 (F.sigma (t + u)) *
        (F.X' 4 (F.sigma (t + u) * (t + u) + z) * F.X 6 (t + u) * F.X' 6 z) := by
    simpa only [mul_assoc] using hEq2
  have hsecond := T.eq_of_mul_eq_mul (a := 2) (c := 3) (b := 6)
    (by norm_num) (by norm_num) (by norm_num) hB1mem hB2mem hT1mem hT2mem hEq3
  have hb : F.X 3 (F.sigma t + F.sigma u) = F.X 3 (F.sigma (t + u)) :=
    mul_left_cancel hsecond.1
  have hEq4 : F.X' 2 (t + u) * F.X 3 (F.sigma t + F.sigma u) *
        F.X' 4 (F.sigma t * t + t * F.sigma u + F.sigma u * u) * (F.X 6 t * F.X 6 u) =
      F.X' 2 (t + u) * F.X 3 (F.sigma (t + u)) *
        F.X' 4 (F.sigma (t + u) * (t + u) + z) * (F.X 6 (t + u) * F.X' 6 z) := by
    simpa only [mul_assoc] using hEq2
  have hthird := T.eq_of_mul_eq_mul (a := 2) (c := 4) (b := 6)
    (by norm_num) (by norm_num) (by norm_num)
    (by
      exact (win T.U 2 4).mul_mem
        ((win T.U 2 4).mul_mem
          (T.U_le_win (by norm_num) (by norm_num)
            (T.Uprime_le 2 (F.X'_mem (by decide : Even (2 : ℤ)) (t + u))))
          (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 3 _)))
        (T.U_le_win (by norm_num) (by norm_num)
          (T.Uprime_le 4 (F.X'_mem (by decide : Even (4 : ℤ)) _))))
    (by
      exact (win T.U 2 4).mul_mem
        ((win T.U 2 4).mul_mem
          (T.U_le_win (by norm_num) (by norm_num)
            (T.Uprime_le 2 (F.X'_mem (by decide : Even (2 : ℤ)) (t + u))))
          (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 3 _)))
        (T.U_le_win (by norm_num) (by norm_num)
          (T.Uprime_le 4 (F.X'_mem (by decide : Even (4 : ℤ)) _))))
    (by
      exact (win T.U 5 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 t))
        (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 u)))
    (by
      exact (win T.U 5 6).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) (F.X_mem 6 (t + u)))
        (T.U_le_win (by norm_num) (by norm_num)
          (T.Uprime_le 6 (F.X'_mem (by decide : Even (6 : ℤ)) z))))
    hEq4
  have hC : F.X' 4 (F.sigma t * t + t * F.sigma u + F.sigma u * u) =
      F.X' 4 (F.sigma (t + u) * (t + u) + z) := by
    have h := hthird.1
    rw [← hb] at h
    exact mul_left_cancel h
  have hS : F.sigma t * t + t * F.sigma u + F.sigma u * u =
      F.sigma (t + u) * (t + u) + z :=
    (F.X'_injective (j := 4) (by decide : Even (4 : ℤ))) hC
  have hz : z = u * F.sigma t := by
    have hz' : z = (F.sigma t * t + t * F.sigma u + F.sigma u * u) +
        F.sigma (t + u) * (t + u) := by
      linear_combination -hS - (F.sigma (t + u) * (t + u)) * F.two_eq_zero
    rw [hz', map_add]
    linear_combination (F.sigma t * t) * F.two_eq_zero +
      (F.sigma u * u) * F.two_eq_zero + (t * F.sigma u) * F.two_eq_zero
  rw [← hz]
  exact hP
theorem X_mul_even {j : ℤ} (hj : Even j) (t u : F.K) :
    F.X j t * F.X j u = F.X j (t + u) * F.X' j (u * F.sigma t) := by
  obtain ⟨k, hk⟩ := hj
  have h := congrArg (MulAut.conj (F.rho ^ (k - 3))) (F.X_mul_even_six t u)
  simp only [map_mul, MulAut.conj_apply, F.conj_rho_X, F.conj_rho_X'] at h
  have h6 : (6 : ℤ) + 2 * (k - 3) = j := by omega
  rwa [h6] at h
theorem X_mul_self_even {j : ℤ} (hj : Even j) (t : F.K) :
    F.X j t * F.X j t = F.X' j (F.sigma t * t) := by
  have h := F.X_mul_even hj t t
  rw [CharTwo.add_self_eq_zero, F.X_zero, one_mul, mul_comm t (F.sigma t)] at h
  exact h
theorem X_inv_even {j : ℤ} (hj : Even j) (t : F.K) :
    (F.X j t)⁻¹ = F.X j t * F.X' j (F.sigma t * t) := by
  have h := F.X_mul_self_even hj t
  calc
    (F.X j t)⁻¹ = F.X j t * (F.X j t * F.X j t)⁻¹ := by group
    _ = F.X j t * (F.X' j (F.sigma t * t))⁻¹ := by rw [h]
    _ = F.X j t * F.X' j (F.sigma t * t) := by rw [F.X'_inv hj]
end OctFrame

end CFSG.GH74.Tits83
