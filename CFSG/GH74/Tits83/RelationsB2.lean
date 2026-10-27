module

public import CFSG.GH74.Tits83.RelationsB

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

theorem comm_X'2_X'8 (t u : F.K) :
    ⁅F.X' 2 t, F.X' 8 u⁆ = F.X' 4 (F.sigma t * u) * F.X 5 (t * u) * F.X' 6 (t * F.sigma u) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hsu : F.sigma u ≠ 0 := (map_ne_zero F.sigma).2 hu
  set d : F.K := t * F.sigma u / u with hd
  have hd0 : d ≠ 0 := div_ne_zero (mul_ne_zero ht hsu) hu
  have hv : F.X' 8 u ∈ T.Uprime 8 := F.X'_mem (by decide) u
  have hv1 : F.X' 8 u ≠ 1 := F.X'_ne_one (by decide) hu
  have hu3 : F.X 3 d ∈ T.U 3 := F.X_mem 3 d
  have hu3ne : F.X 3 d ≠ 1 := F.X_ne_one 3 hd0
  have hm8 : (T.mu 8 (F.X' 8 u))⁻¹ = T.mu 8 (F.X' 8 u) :=
    inv_eq_of_mul_eq_one_right (F.mu_X'_mul_self (by decide) hu)
  have hcomm : ⁅F.X 3 d, F.X' 8 u⁆ = F.X' 6 (d * u) := by
    have := F.r3 2 (by decide) d u
    norm_num at this
    exact this
  have hu' : F.X' 2 t =
      (T.mu 8 (F.X' 8 u))⁻¹ * ⁅F.X 3 d, F.X' 8 u⁆ * T.mu 8 (F.X' 8 u) := by
    rw [hcomm, hm8]
    have := F.mu_X'_conj_X' (i := 8) (by decide) hu (j := 6) (by decide) (d * u)
    norm_num [wtX'] at this
    rw [hm8] at this
    rw [this, show (18 : ℤ) = 2 + 16 by norm_num, F.X'_add_sixteen]
    congr 1
    rw [hd]
    field_simp
  have h := T.lemma38_ii F.hT hv hv1 hu3 hu3ne hu'
  set A : G := F.X' 4 (F.sigma t * u) with hAdef
  set B : G := F.X 5 (t * u) with hBdef
  set C : G := F.X' 6 (t * F.sigma u) with hCdef
  have hA : T.mu 2 (F.X' 2 t) * (F.X' 8 u)⁻¹ * (T.mu 2 (F.X' 2 t))⁻¹ = A := by
    rw [hAdef, F.X'_inv (j := 8) (by decide)]
    have := F.mu_X'_conj_X' (i := 2) (by decide) ht (j := 8) (by decide) u
    norm_num [wtX'] at this
    rw [this]
    congr 1
    field_simp
  have hB : T.mu 8 (F.X' 8 u) * F.X 3 d * (T.mu 8 (F.X' 8 u))⁻¹ = B := by
    rw [hBdef]
    have := F.mu_X'_conj_X (i := 8) (by decide) hu (j := 3) d
    norm_num [wtX] at this
    rw [this, show (21 : ℤ) = 5 + 16 by norm_num, F.X_add_sixteen]
    congr 1
    rw [hd]
    field_simp
  have hC : T.mu 8 (F.X' 8 u) * F.X' 2 t * (T.mu 8 (F.X' 8 u))⁻¹ = C := by
    rw [hCdef]
    have := F.mu_X'_conj_X' (i := 8) (by decide) hu (j := 2) (by decide) t
    norm_num [wtX'] at this
    rw [this, show (22 : ℤ) = 6 + 16 by norm_num, F.X'_add_sixteen]
    congr 1
    field_simp
  rw [hA, hB, hC] at h
  have hAinv : A⁻¹ = A := by
    rw [hAdef]
    exact F.X'_inv (j := 4) (by decide) _
  have hBinv : B⁻¹ = B := by
    rw [hBdef]
    exact F.X_inv_odd (j := 5) (by decide) _
  have hCinv : C⁻¹ = C := by
    rw [hCdef]
    exact F.X'_inv (j := 6) (by decide) _
  have hAB : A * B = B * A := by
    rw [hAdef, hBdef]
    exact T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 5 _)
  have hAC : A * C = C * A := by
    rw [hAdef, hCdef]
    exact T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (T.Uprime_le 6 (F.X'_mem (by decide) _))
  have hBC : B * C = C * B := by
    rw [hBdef, hCdef]
    exact (T.Uprime_comm (j := 6) (k := 5) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 5 _)).symm
  have hprod : (A * B * C)⁻¹ = A * B * C := by
    rw [mul_inv_rev, mul_inv_rev, hAinv, hBinv, hCinv]
    calc C * (B * A) = C * (A * B) := by rw [← hAB]
      _ = (C * A) * B := by rw [← mul_assoc]
      _ = (A * C) * B := by rw [← hAC]
      _ = A * (C * B) := by rw [mul_assoc]
      _ = A * (B * C) := by rw [← hBC]
      _ = (A * B) * C := by rw [← mul_assoc]
  calc ⁅F.X' 2 t, F.X' 8 u⁆ = ⁅F.X' 8 u, F.X' 2 t⁆⁻¹ := by rw [← commutatorElement_inv]
    _ = (A * B * C)⁻¹ := by rw [h]
    _ = A * B * C := hprod
    _ = F.X' 4 (F.sigma t * u) * F.X 5 (t * u) * F.X' 6 (t * F.sigma u) := by
      rw [hAdef, hBdef, hCdef]

theorem r12 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X' (2 + s) t, F.X' (8 + s) u⁆ =
      F.X' (4 + s) (F.sigma t * u) * F.X (5 + s) (t * u) * F.X' (6 + s) (t * F.sigma u) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ k)) (F.comm_X'2_X'8 t u)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv, F.conj_rho_X,
    F.conj_rho_X'] at h
  rwa [show (2 : ℤ) + 2 * k = 2 + s by omega, show (8 : ℤ) + 2 * k = 8 + s by omega,
    show (4 : ℤ) + 2 * k = 4 + s by omega, show (5 : ℤ) + 2 * k = 5 + s by omega,
    show (6 : ℤ) + 2 * k = 6 + s by omega] at h

theorem comm_X0_X'6 (t u : F.K) :
    ⁅F.X 0 t, F.X' 6 u⁆ = F.X' 2 (F.sigma t * t ^ 2 * u) * F.X' 4 (F.sigma t * t * F.sigma u) *
      F.X 5 (t * u) := by
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
  set d : F.K := F.sigma t * t * u with hd
  have hd0 : d ≠ 0 := mul_ne_zero (mul_ne_zero hst ht) hu
  have hsc : F.sigma c = (t ^ 2 * F.sigma t)⁻¹ := by
    rw [hc, map_inv₀, map_mul, F.sigma_sigma]
  have hct : c / F.sigma c = t := by
    rw [hsc, hc]
    field_simp
  have hv : F.X' 8 c ∈ T.Uprime 8 := F.X'_mem (by decide) c
  have hv1 : F.X' 8 c ≠ 1 := F.X'_ne_one (by decide) hc0
  have hu3 : F.X 3 d ∈ T.U 3 := F.X_mem 3 d
  have hu3ne : F.X 3 d ≠ 1 := F.X_ne_one 3 hd0
  have hm8 : (T.mu 8 (F.X' 8 c))⁻¹ = T.mu 8 (F.X' 8 c) :=
    inv_eq_of_mul_eq_one_right (F.mu_X'_mul_self (by decide) hc0)
  have hm3 : (T.mu 3 (F.X 3 d))⁻¹ = T.mu 3 (F.X 3 d) :=
    inv_eq_of_mul_eq_one_right (F.mu_X_mul_self 3 hd0)
  have hnu : T.nu 8 (F.X' 8 c) = (F.X 0 t)⁻¹ := by
    rw [F.nu_X' (by decide) hc0]
    rw [show (8 : ℤ) + 8 = 0 + 16 by norm_num, F.X_add_sixteen, hct]
  have hy : (T.mu 3 (F.X 3 d))⁻¹ * F.X' 8 c * T.mu 3 (F.X 3 d) = F.X' 6 u := by
    have := F.mu_X_odd_conj_X' (i := 3) (by decide) hd0 (j := 8) (by decide) c
    norm_num [wtX'] at this
    rw [hm3] at this ⊢
    rw [this]
    congr 1
    rw [hd, hc]
    field_simp
  have h := T.lemma34_ii F.hT hu3 hu3ne hv hv1
  rw [hnu, hy] at h
  set A : G := F.X' 2 (F.sigma t * t ^ 2 * u) with hAdef
  set B : G := F.X 3 (F.sigma t * t * u) with hBdef
  set C : G := F.X 5 (t * u) with hCdef
  set D : G := F.X' 4 (F.sigma t * t * F.sigma u) with hDdef
  have hA0 : T.mu 8 (F.X' 8 c) * F.X' 6 u * (T.mu 8 (F.X' 8 c))⁻¹ = A := by
    rw [hAdef]
    have := F.mu_X'_conj_X' (i := 8) (by decide) hc0 (j := 6) (by decide) u
    norm_num [wtX'] at this
    rw [this, show (18 : ℤ) = 2 + 16 by norm_num, F.X'_add_sixteen]
    congr 1
    rw [hsc]
    field_simp
  have hB0 : (F.X 3 d)⁻¹ = B := by
    rw [hBdef, F.X_inv_odd (j := 3) (by decide), hd]
  have hC0 : T.mu 8 (F.X' 8 c) * F.X 3 d * (T.mu 8 (F.X' 8 c))⁻¹ = C := by
    rw [hCdef]
    have := F.mu_X'_conj_X (i := 8) (by decide) hc0 (j := 3) d
    norm_num [wtX] at this
    rw [this, show (21 : ℤ) = 5 + 16 by norm_num, F.X_add_sixteen]
    congr 1
    rw [hd, hsc, hc]
    field_simp
  rw [hA0, hB0, hC0] at h
  have hbc : ⁅F.X' 0 (F.sigma t * t), F.X' 6 u⁆ = A * B * D := by
    have := F.r12 (-2) (by decide) (F.sigma t * t) u
    norm_num at this
    rw [show F.sigma (F.sigma t) = t ^ 2 from F.sigma_sigma t] at this
    rw [this, hAdef, hBdef, hDdef]
    congr 3 <;> ring
  have hAinv : A⁻¹ = A := by
    rw [hAdef]
    exact F.X'_inv (j := 2) (by decide) _
  have hBinv : B⁻¹ = B := by
    rw [hBdef]
    exact F.X_inv_odd (j := 3) (by decide) _
  have hDinv : D⁻¹ = D := by
    rw [hDdef]
    exact F.X'_inv (j := 4) (by decide) _
  have hA2 : A * A = 1 := by
    nth_rewrite 1 [← hAinv]
    exact inv_mul_cancel A
  have hB2 : B * B = 1 := by
    nth_rewrite 1 [← hBinv]
    exact inv_mul_cancel B
  have hAB : A * B = B * A := by
    rw [hAdef, hBdef]
    exact T.Uprime_comm (j := 2) (k := 3) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 3 _)
  have hAD : A * D = D * A := by
    rw [hAdef, hDdef]
    exact T.Uprime_comm (j := 2) (k := 4) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (T.Uprime_le 4 (F.X'_mem (by decide) _))
  have hAa : F.X 0 t * A * (F.X 0 t)⁻¹ = A := by
    rw [hAdef]
    have hcomm := T.Uprime_comm (j := 2) (k := 0) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) (F.sigma t * t ^ 2 * u)) (F.X_mem 0 t)
    calc F.X 0 t * F.X' 2 (F.sigma t * t ^ 2 * u) * (F.X 0 t)⁻¹
        = (F.X' 2 (F.sigma t * t ^ 2 * u) * F.X 0 t) * (F.X 0 t)⁻¹ := by rw [hcomm.symm]
      _ = F.X' 2 (F.sigma t * t ^ 2 * u) := by group
  have hDa : F.X 0 t * D * (F.X 0 t)⁻¹ = D := by
    rw [hDdef]
    have hcomm := T.Uprime_comm (j := 4) (k := 0) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) (F.sigma t * t * F.sigma u)) (F.X_mem 0 t)
    calc F.X 0 t * F.X' 4 (F.sigma t * t * F.sigma u) * (F.X 0 t)⁻¹
        = (F.X' 4 (F.sigma t * t * F.sigma u) * F.X 0 t) * (F.X 0 t)⁻¹ := by rw [hcomm.symm]
      _ = F.X' 4 (F.sigma t * t * F.sigma u) := by group
  have haB : F.X 0 t * B * (F.X 0 t)⁻¹ = A * B := by
    have hcomm : ⁅F.X 0 t, B⁆ = A := by
      rw [hBdef, hAdef]
      have := F.r9 (-2) (by decide) t (F.sigma t * t * u)
      norm_num at this
      rw [this]
      congr 1
      ring
    calc F.X 0 t * B * (F.X 0 t)⁻¹ = (F.X 0 t * B * (F.X 0 t)⁻¹ * B⁻¹) * B := by group
      _ = ⁅F.X 0 t, B⁆ * B := rfl
      _ = A * B := by rw [hcomm]
  have hp : F.X 0 t * ⁅F.X' 0 (F.sigma t * t), F.X' 6 u⁆ * (F.X 0 t)⁻¹ = B * D := by
    rw [hbc]
    calc F.X 0 t * (A * B * D) * (F.X 0 t)⁻¹
        = (F.X 0 t * A * (F.X 0 t)⁻¹) * (F.X 0 t * B * (F.X 0 t)⁻¹) *
            (F.X 0 t * D * (F.X 0 t)⁻¹) := by group
      _ = A * (A * B) * D := by rw [hAa, haB, hDa]
      _ = (A * A) * B * D := by group
      _ = B * D := by rw [hA2]; group
  have hainv : (F.X 0 t)⁻¹ = F.X 0 t * F.X' 0 (F.sigma t * t) :=
    F.X_inv_even (by decide) t
  have hsb : ⁅F.X 0 t * F.X' 0 (F.sigma t * t), F.X' 6 u⁆ =
      F.X 0 t * ⁅F.X' 0 (F.sigma t * t), F.X' 6 u⁆ * (F.X 0 t)⁻¹ *
        ⁅F.X 0 t, F.X' 6 u⁆ := by
    simp only [commutatorElement_def]
    group
  have hg' : ⁅F.X 0 t * F.X' 0 (F.sigma t * t), F.X' 6 u⁆ = A * B * C := by
    rw [← hainv]
    exact h
  have h1 : F.X 0 t * ⁅F.X' 0 (F.sigma t * t), F.X' 6 u⁆ * (F.X 0 t)⁻¹ *
      ⁅F.X 0 t, F.X' 6 u⁆ = A * B * C := hsb.symm.trans hg'
  rw [hp] at h1
  have hq : ⁅F.X 0 t, F.X' 6 u⁆ = (B * D)⁻¹ * (A * B * C) := by
    rw [← h1]
    group
  calc ⁅F.X 0 t, F.X' 6 u⁆ = (B * D)⁻¹ * (A * B * C) := hq
    _ = D * B * (A * B * C) := by rw [mul_inv_rev, hBinv, hDinv]
    _ = D * B * A * B * C := by group
    _ = D * (B * A) * B * C := by group
    _ = D * (A * B) * B * C := by rw [← hAB]
    _ = D * A * (B * B) * C := by group
    _ = D * A * C := by rw [hB2]; group
    _ = A * D * C := by rw [← hAD]

theorem r14 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (2 + s) t, F.X' (8 + s) u⁆ =
      F.X' (4 + s) (F.sigma t * t ^ 2 * u) * F.X' (6 + s) (F.sigma t * t * F.sigma u) *
        F.X (7 + s) (t * u) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ (k + 1))) (F.comm_X0_X'6 t u)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv, F.conj_rho_X,
    F.conj_rho_X'] at h
  rwa [show (0 : ℤ) + 2 * (k + 1) = 2 + s by omega,
    show (6 : ℤ) + 2 * (k + 1) = 8 + s by omega,
    show (2 : ℤ) + 2 * (k + 1) = 4 + s by omega,
    show (4 : ℤ) + 2 * (k + 1) = 6 + s by omega,
    show (5 : ℤ) + 2 * (k + 1) = 7 + s by omega] at h

theorem r13 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X' (2 + s) t, F.X (8 + s) u⁆ =
      F.X (3 + s) (t * u) * F.X' (4 + s) (F.sigma t * F.sigma u * u) *
        F.X' (6 + s) (t * F.sigma u * u ^ 2) := by
  have h0 := congrArg (MulAut.conj F.a) (F.comm_X0_X'6 u t)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv, F.conj_a_X] at h0
  rw [F.conj_a_X' (j := 6) (by decide), F.conj_a_X' (j := 2) (by decide),
    F.conj_a_X' (j := 4) (by decide)] at h0
  norm_num at h0
  have h1 : ⁅F.X' 4 t, F.X 10 u⁆ =
      F.X 5 (t * u) * F.X' 6 (F.sigma t * F.sigma u * u) * F.X' 8 (t * F.sigma u * u ^ 2) := by
    rw [← commutatorElement_inv, h0, mul_inv_rev, mul_inv_rev]
    rw [F.X_inv_odd (j := 5) (by decide), F.X'_inv (j := 6) (by decide),
      F.X'_inv (j := 8) (by decide)]
    rw [show u * t = t * u by ring,
      show F.sigma u * u * F.sigma t = F.sigma t * F.sigma u * u by ring,
      show F.sigma u * u ^ 2 * t = t * F.sigma u * u ^ 2 by ring, ← mul_assoc]
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ (k - 1))) h1
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv, F.conj_rho_X,
    F.conj_rho_X'] at h
  rwa [show (4 : ℤ) + 2 * (k - 1) = 2 + s by omega,
    show (10 : ℤ) + 2 * (k - 1) = 8 + s by omega,
    show (5 : ℤ) + 2 * (k - 1) = 3 + s by omega,
    show (6 : ℤ) + 2 * (k - 1) = 4 + s by omega,
    show (8 : ℤ) + 2 * (k - 1) = 6 + s by omega] at h

theorem comm_X2_X4 (t u : F.K) : ⁅F.X 2 t, F.X 4 u⁆ = F.X 3 (t * u) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hmem : ⁅F.X 2 t, F.X 4 u⁆ ∈ T.U 3 := by
    have h := T.commutator_mem_win (j := 2) (a := 4) (b := 4) (by norm_num) (by norm_num)
      (by norm_num) (F.X_mem 2 t) (by rw [T.win_self]; exact F.X_mem 4 u)
    simpa [T.win_self] using h
  obtain ⟨z, hz⟩ := (F.bij_odd_X (j := 3) (by decide)).2
    ⟨⁅F.X 2 t, F.X 4 u⁆, hmem⟩
  have hzX : ⁅F.X 2 t, F.X 4 u⁆ = F.X 3 z := (congrArg Subtype.val hz).symm
  set e : G := F.X' 8 1 with hedef
  set a1 : G := F.X' 4 (F.sigma t * t ^ 2) with ha1def
  set a2 : G := F.X' 6 (F.sigma t * t) with ha2def
  set x7 : G := F.X 7 t with hx7def
  set R : G := a1 * a2 * x7 with hRdef
  have h14 : ⁅F.X 2 t, e⁆ = a1 * a2 * x7 := by
    rw [hedef, ha1def, ha2def, hx7def]
    have := F.r14 0 (by decide) t 1
    norm_num at this
    simpa using this
  have h74 : ⁅F.X 7 t, F.X 4 u⁆ = F.X' 6 (t * u) := by
    have h0 := congrArg (MulAut.conj F.a) (F.r2 2 (by decide) t u)
    simp only [map_commutatorElement, MulAut.conj_apply, F.conj_a_X] at h0
    norm_num at h0
    rw [F.conj_a_X' (j := 4) (by decide)] at h0
    exact h0
  have h3e : ⁅F.X 3 z, e⁆ = F.X' 6 z := by
    rw [hedef]
    have := F.r3 2 (by decide) z 1
    norm_num at this
    simpa using this
  have h12 : a1 * a2 = a2 * a1 := by
    rw [ha1def, ha2def]
    exact T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (T.Uprime_le 6 (F.X'_mem (by decide) _))
  have h1x : a1 * x7 = x7 * a1 := by
    rw [ha1def, hx7def]
    exact T.Uprime_comm (j := 4) (k := 7) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 7 t)
  have h2x : a2 * x7 = x7 * a2 := by
    rw [ha2def, hx7def]
    exact T.Uprime_comm (j := 6) (k := 7) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 7 t)
  have hRinv : R⁻¹ = R := by
    rw [hRdef, mul_inv_rev, mul_inv_rev]
    rw [ha1def, ha2def, hx7def, F.X'_inv (j := 4) (by decide),
      F.X'_inv (j := 6) (by decide), F.X_inv_odd (j := 7) (by decide)]
    calc F.X 7 t * (F.X' 6 (F.sigma t * t) * F.X' 4 (F.sigma t * t ^ 2))
        = F.X 7 t * (F.X' 4 (F.sigma t * t ^ 2) * F.X' 6 (F.sigma t * t)) := by
          rw [← h12]
      _ = (F.X 7 t * F.X' 4 (F.sigma t * t ^ 2)) * F.X' 6 (F.sigma t * t) := by
          rw [← mul_assoc]
      _ = (F.X' 4 (F.sigma t * t ^ 2) * F.X 7 t) * F.X' 6 (F.sigma t * t) := by
          rw [← h1x]
      _ = F.X' 4 (F.sigma t * t ^ 2) * (F.X 7 t * F.X' 6 (F.sigma t * t)) := by
          rw [mul_assoc]
      _ = F.X' 4 (F.sigma t * t ^ 2) * (F.X' 6 (F.sigma t * t) * F.X 7 t) := by
          rw [← h2x]
      _ = F.X' 4 (F.sigma t * t ^ 2) * F.X' 6 (F.sigma t * t) * F.X 7 t := by
          rw [← mul_assoc]
  have hRe : ⁅e, F.X 2 t⁆ = R := by
    rw [← commutatorElement_inv, h14]
    exact hRinv
  have hconjX2 : e * F.X 2 t * e⁻¹ = R * F.X 2 t := by
    calc e * F.X 2 t * e⁻¹ = (e * F.X 2 t * e⁻¹ * (F.X 2 t)⁻¹) * F.X 2 t := by group
      _ = ⁅e, F.X 2 t⁆ * F.X 2 t := rfl
      _ = R * F.X 2 t := by rw [hRe]
  have h3e' : ⁅e, F.X 3 z⁆ = F.X' 6 z := by
    rw [← commutatorElement_inv, h3e, F.X'_inv (j := 6) (by decide)]
  have hconjX3 : e * F.X 3 z * e⁻¹ = F.X' 6 z * F.X 3 z := by
    calc e * F.X 3 z * e⁻¹ = (e * F.X 3 z * e⁻¹ * (F.X 3 z)⁻¹) * F.X 3 z := by group
      _ = ⁅e, F.X 3 z⁆ * F.X 3 z := rfl
      _ = F.X' 6 z * F.X 3 z := by rw [h3e']
  have hec : e * F.X 4 u * e⁻¹ = F.X 4 u := by
    have hcomm := T.Uprime_comm (j := 8) (k := 4) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) 1) (F.X_mem 4 u)
    rw [hedef]
    calc F.X' 8 1 * F.X 4 u * (F.X' 8 1)⁻¹
        = (F.X 4 u * F.X' 8 1) * (F.X' 8 1)⁻¹ := by rw [hcomm]
      _ = F.X 4 u := by group
  have hcm : ∀ {p x y : G}, p * x = x * p → p * y = y * p →
      p * (x * y) = (x * y) * p := by
    intro p x y hpx hpy
    calc p * (x * y) = (p * x) * y := by group
      _ = (x * p) * y := by rw [hpx]
      _ = x * (p * y) := by group
      _ = x * (y * p) := by rw [hpy]
      _ = (x * y) * p := by group
  have hx7x3 : x7 * F.X 3 z * x7⁻¹ = F.X 3 z := by
    rw [hx7def]
    have hcomm := T.comm_odd_add_four F.hT (j := 3) (by decide)
      (F.X_mem 3 z) (F.X_mem 7 t)
    calc F.X 7 t * F.X 3 z * (F.X 7 t)⁻¹
        = (F.X 3 z * F.X 7 t) * (F.X 7 t)⁻¹ := by rw [hcomm.symm]
      _ = F.X 3 z := by group
  have hrc : ⁅x7 * F.X 2 t, F.X 4 u⁆ = F.X 3 z * F.X' 6 (t * u) := by
    have hmul : ⁅x7 * F.X 2 t, F.X 4 u⁆ =
        x7 * ⁅F.X 2 t, F.X 4 u⁆ * x7⁻¹ * ⁅x7, F.X 4 u⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hmul, hzX, hx7def, h74, hx7x3]
  have hdrop : ∀ {p q r c d : G}, p * c = c * p → q * c = c * q →
      p * d = d * p → q * d = d * q → ⁅r, c⁆ = d → ⁅p * q * r, c⁆ = d := by
    intro p q r c d hpc hqc hpd hqd hd
    have hmul1 : ⁅p * q * r, c⁆ = p * ⁅q * r, c⁆ * p⁻¹ * ⁅p, c⁆ := by
      simp only [commutatorElement_def]
      group
    have hmul2 : ⁅q * r, c⁆ = q * ⁅r, c⁆ * q⁻¹ * ⁅q, c⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hmul1, hmul2, hd, commutatorElement_eq_one_iff_mul_comm.mpr hpc,
      commutatorElement_eq_one_iff_mul_comm.mpr hqc]
    simp only [mul_one]
    calc p * (q * d * q⁻¹) * p⁻¹ = p * q * d * q⁻¹ * p⁻¹ := by group
      _ = p * (q * d) * q⁻¹ * p⁻¹ := by group
      _ = p * (d * q) * q⁻¹ * p⁻¹ := by rw [hqd]
      _ = p * d * p⁻¹ := by group
      _ = (d * p) * p⁻¹ := by rw [hpd]
      _ = d := by group
  have ha1c : a1 * F.X 4 u = F.X 4 u * a1 := by
    rw [ha1def]
    exact T.Uprime_comm (j := 4) (k := 4) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 4 u)
  have ha2c : a2 * F.X 4 u = F.X 4 u * a2 := by
    rw [ha2def]
    exact T.Uprime_comm (j := 6) (k := 4) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 4 u)
  have ha1d : a1 * (F.X 3 z * F.X' 6 (t * u)) =
      (F.X 3 z * F.X' 6 (t * u)) * a1 := by
    rw [ha1def]
    exact hcm
      (T.Uprime_comm (j := 4) (k := 3) (by norm_num) (by norm_num)
        (F.X'_mem (by decide) _) (F.X_mem 3 z))
      (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num)
        (F.X'_mem (by decide) _) (T.Uprime_le 6 (F.X'_mem (by decide) _)))
  have ha2d : a2 * (F.X 3 z * F.X' 6 (t * u)) =
      (F.X 3 z * F.X' 6 (t * u)) * a2 := by
    rw [ha2def]
    exact hcm
      (T.Uprime_comm (j := 6) (k := 3) (by norm_num) (by norm_num)
        (F.X'_mem (by decide) _) (F.X_mem 3 z))
      (T.Uprime_comm (j := 6) (k := 6) (by norm_num) (by norm_num)
        (F.X'_mem (by decide) _) (T.Uprime_le 6 (F.X'_mem (by decide) _)))
  have hRx : ⁅a1 * a2 * (x7 * F.X 2 t), F.X 4 u⁆ = F.X 3 z * F.X' 6 (t * u) :=
    hdrop ha1c ha2c ha1d ha2d hrc
  have hRxR : ⁅R * F.X 2 t, F.X 4 u⁆ = F.X 3 z * F.X' 6 (t * u) := by
    simpa [hRdef, mul_assoc] using hRx
  have hconjeq := congrArg (MulAut.conj e) hzX
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, hconjX2, hconjX3,
    hec] at hconjeq
  have hz6eq : F.X' 6 z * F.X 3 z = F.X 3 z * F.X' 6 (t * u) := by
    rw [← hconjeq, hRxR]
  have hx6comm : F.X' 6 (t * u) * F.X 3 z = F.X 3 z * F.X' 6 (t * u) :=
    T.Uprime_comm (j := 6) (k := 3) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) _) (F.X_mem 3 z)
  rw [← hx6comm] at hz6eq
  have hz6 : F.X' 6 z = F.X' 6 (t * u) := mul_right_cancel hz6eq
  have hz_eq : z = t * u := F.X'_injective (j := 6) (by decide) hz6
  rw [hzX, hz_eq]

theorem r8 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (2 + s) t, F.X (4 + s) u⁆ = F.X (3 + s) (t * u) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ k)) (F.comm_X2_X4 t u)
  simp only [map_commutatorElement, MulAut.conj_apply, map_mul, map_inv, F.conj_rho_X,
    F.conj_rho_X'] at h
  rwa [show (2 : ℤ) + 2 * k = 2 + s by omega, show (4 : ℤ) + 2 * k = 4 + s by omega,
    show (3 : ℤ) + 2 * k = 3 + s by omega] at h

end OctFrame

end CFSG.GH74.Tits83
