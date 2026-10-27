module

public import CFSG.GH74.Tits83.RelationsC
public import CFSG.GH74.Tits83.OctCoord
public import CFSG.GH74.Tits83.RelationsB2

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

private theorem X6_mul_X3_of_comm (d a e : F.K)
    (h : ⁅F.X 3 d, F.X 6 a⁆ = F.X' 4 e) :
    F.X 6 a * F.X 3 d = F.X' 4 e * F.X 3 d * F.X 6 a := by
  have h3sq : F.X 3 d * F.X 3 d = 1 := by
    calc
      F.X 3 d * F.X 3 d = F.X 3 d * (F.X 3 d)⁻¹ := by
        rw [F.X_inv_odd (j := 3) (by decide)]
      _ = 1 := mul_inv_cancel _
  have hstep : F.X 6 a * F.X 3 d = F.X 3 d * ⁅F.X 3 d, F.X 6 a⁆ * F.X 6 a := by
    rw [commutatorElement_def, F.X_inv_odd (j := 3) (by decide)]
    rw [show F.X 3 d * (F.X 3 d * F.X 6 a * F.X 3 d * (F.X 6 a)⁻¹) * F.X 6 a =
      (F.X 3 d * F.X 3 d) * F.X 6 a * F.X 3 d by group]
    rw [h3sq, one_mul]
  calc
    F.X 6 a * F.X 3 d = F.X 3 d * ⁅F.X 3 d, F.X 6 a⁆ * F.X 6 a := hstep
    _ = F.X 3 d * F.X' 4 e * F.X 6 a := by rw [h]
    _ = F.X' 4 e * F.X 3 d * F.X 6 a := by
      rw [(T.Uprime_comm (j := 4) (k := 3) (by norm_num) (by norm_num)
        (F.X'_mem (by decide) e) (F.X_mem 3 d)).symm]

private theorem X6_mul_X4_inv_of_comm (c a d : F.K)
    (h : ⁅F.X 4 c, F.X 6 a⁆ = F.X 5 d) :
    F.X 6 a * (F.X 4 c)⁻¹ = (F.X 4 c)⁻¹ * F.X 5 d * F.X 6 a := by
  calc
    F.X 6 a * (F.X 4 c)⁻¹ = (F.X 4 c)⁻¹ * ⁅F.X 4 c, F.X 6 a⁆ * F.X 6 a := by
      rw [commutatorElement_def]
      group
    _ = (F.X 4 c)⁻¹ * F.X 5 d * F.X 6 a := by rw [h]

theorem comm_X2_X8 (t u : F.K) :
    ⁅F.X 2 t, F.X 8 u⁆ =
      F.X 3 (F.sigma t * t * u) * (F.X 4 (F.sigma t * u))⁻¹ * F.X 6 (t * F.sigma u) *
        F.X 7 (t * F.sigma u * u) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hst : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  have hsu : F.sigma u ≠ 0 := (map_ne_zero F.sigma).2 hu
  set c : F.K := (F.sigma u * u)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero hsu hu)
  set a : F.K := t * F.sigma u with ha
  have ha0 : a ≠ 0 := mul_ne_zero ht hsu
  have hsa : F.sigma a = F.sigma t * u ^ 2 := by
    rw [ha, map_mul, F.sigma_sigma]
  set b : F.K := a * u with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha0 hu
  have hsb : F.sigma b = F.sigma t * u ^ 2 * F.sigma u := by
    rw [hb, map_mul, hsa]
  set D1 : F.K := c * F.sigma a * a ^ 2 with hD1
  set D2 : F.K := F.sigma c * F.sigma a * a with hD2
  set D3 : F.K := F.sigma b * b * c ^ 2 with hD3
  set C : F.K := F.sigma b * c with hC
  set D4 : F.K := F.sigma b * b * F.sigma c with hD4
  set D5 : F.K := F.sigma b * b * c with hD5
  set F1 : G := F.X' 4 D1 with hF1
  set F2 : G := F.X' 2 D2 with hF2
  set G1 : G := F.X 1 (c * a) with hG1
  set E1 : G := F.X 1 (b * F.sigma c) with hE1
  set E2 : G := F.X 2 (b * c) with hE2
  set E3 : G := F.X 3 D3 with hE3
  set E4 : G := (F.X 4 C)⁻¹ with hE4
  set E5 : G := F.X 5 D4 with hE5
  set E6 : G := F.X' 6 D5 with hE6
  set X6 : G := F.X 6 a with hX6
  set X7 : G := F.X 7 b with hX7
  have hca : c * a = b * F.sigma c := by
    rw [hc, hb, ha]
    simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
  have hbc : b * c = t := by
    rw [hc, hb, ha]
    try simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
  have hD2t : D2 = F.sigma t * t := by
    rw [hD2, hc, hsa, map_inv₀, map_mul, F.sigma_sigma]
    try simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
    try ring
  have hD3a : D3 * a = D1 := by
    rw [hD3, hD1, hc, hb, ha, hsa, hsb]
    try simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
    try ring
  have hCa : C * a = D4 := by
    rw [hC, hD4, hc, hb, ha, hsb]
    try simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
    try ring
  have hD5sa : D5 = F.sigma a * a := by
    rw [hD5, hc, hb, ha, hsb]
    try simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
    try ring
  have hD3t : D3 = F.sigma t * t * u := by
    rw [hD3, hc, hb, ha, hsb]
    try simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
    try ring
  have hCt : C = F.sigma t * u := by
    rw [hC, hc, hb, ha, hsb]
    try simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
    try ring
  have hbt : b = t * F.sigma u * u := by rw [hb, ha]
  set y : G := F.X 8 u with hy
  set y' : G := F.X' 0 c with hyp
  set x : G := F.X 2 t with hx
  have hy1 : y ≠ 1 := F.X_ne_one 8 hu
  have hyp1 : y' ≠ 1 := F.X'_ne_one (by decide) hc0
  have hypmem : y' ∈ T.Uprime 0 := F.X'_mem (by decide) c
  have hypinv : y' * y' = 1 := by
    rw [hyp]
    calc
      F.X' 0 c * F.X' 0 c = F.X' 0 c * (F.X' 0 c)⁻¹ := by
        rw [F.X'_inv (by decide) c]
      _ = 1 := mul_inv_cancel _
  have hnu8 : T.nu 8 y = y' := by
    rw [hy, hyp, F.nu_X_even (j := 8) (by decide) hu,
      show (8 : ℤ) + 8 = 0 + 16 by norm_num, F.X'_add_sixteen]
  have hnu'0 : T.nu' 0 y' = y := by
    have h := (T.mu_nu (by norm_num : 3 ≤ (8 : ℕ)) (i := 8)
      (F.X_mem 8 u) (F.X_ne_one 8 hu)).2
    rw [hnu8] at h
    norm_num at h
    rw [show (16 : ℤ) = 0 + 2 * ↑(8 : ℕ) * 1 by norm_num,
      T.nu'_add_two_mul (by norm_num : 3 ≤ (8 : ℕ)) (0 : ℤ) 1 y'] at h
    simpa [← hy] using h
  have hnu0 : T.nu 0 y' = y⁻¹ := by
    have h := T.lemma316_i F.hT (j := 0) (by decide) hypmem hyp1
    rwa [hnu'0] at h
  have hm : T.mu 8 y = T.mu 0 y' := by
    have h := (T.mu_nu (by norm_num : 3 ≤ (8 : ℕ)) (i := 8)
      (F.X_mem 8 u) (F.X_ne_one 8 hu)).1
    rw [hnu8] at h
    norm_num at h
    rw [show (16 : ℤ) = 0 + 2 * ↑(8 : ℕ) * 1 by norm_num,
      T.mu_add_two_mul (by norm_num : 3 ≤ (8 : ℕ)) (0 : ℤ) 1 y'] at h
    exact h.symm
  have hmdec : T.mu 0 y' = y⁻¹ * y' * y := by
    rw [TitsSystem.mu, hnu0, hnu'0]
  have hmx : T.mu 0 y' * x * (T.mu 0 y')⁻¹ = X6 := by
    rw [hX6, hyp, hx]
    have h := F.mu_X'_conj_X (i := 0) (by decide) hc0 (j := 2) t
    rw [h]
    congr 1
    rw [hc, ha]
    norm_num [wtX]
    simp only [map_mul, map_inv₀, F.sigma_sigma]
    field_simp
  have hyX6 : ⁅y, X6⁆ = X7 := by
    rw [hX6, hX7]
    have h := F.r8 4 (by decide) a u
    norm_num at h
    calc
      ⁅F.X 8 u, F.X 6 a⁆ = ⁅F.X 6 a, F.X 8 u⁆⁻¹ :=
        (commutatorElement_inv (F.X 6 a) (F.X 8 u)).symm
      _ = (F.X 7 (a * u))⁻¹ := by rw [h]
      _ = F.X 7 (a * u) := F.X_inv_odd (j := 7) (by decide) _
      _ = F.X 7 b := by rw [hb]
  have hconj3 : y * X6 * y⁻¹ = X7 * X6 := by
    calc
      y * X6 * y⁻¹ = ⁅y, X6⁆ * X6 := by
        rw [commutatorElement_def]
        group
      _ = X7 * X6 := by rw [hyX6]

  have hmm : T.mu 0 y' * T.mu 0 y' = 1 := by
    rw [hmdec]
    rw [show y⁻¹ * y' * y * (y⁻¹ * y' * y) = y⁻¹ * (y' * y') * y by group, hypinv]
    group
  have hm1 : y * T.mu 0 y' = y' * y := by rw [hmdec]; group
  have hm2 : T.mu 0 y' * y⁻¹ = y⁻¹ * y' := by rw [hmdec]; group
  have hmxinv : T.mu 0 y' * x⁻¹ * (T.mu 0 y')⁻¹ = X6⁻¹ := by
    calc
      T.mu 0 y' * x⁻¹ * (T.mu 0 y')⁻¹ =
          (T.mu 0 y' * x * (T.mu 0 y')⁻¹)⁻¹ := by group
      _ = X6⁻¹ := by rw [hmx]
  have hconj3inv : y * X6⁻¹ * y⁻¹ = X6⁻¹ * X7 := by
    calc
      y * X6⁻¹ * y⁻¹ = (y * X6 * y⁻¹)⁻¹ := by group
      _ = (X7 * X6)⁻¹ := by rw [hconj3]
      _ = X6⁻¹ * X7⁻¹ := by rw [mul_inv_rev]
      _ = X6⁻¹ * X7 := by rw [hX7, F.X_inv_odd (j := 7) (by decide)]
  have h4 : ⁅x, y⁆ = x * (y' * X6⁻¹ * X7 * y'⁻¹) := by
    have hyinv : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hypinv
    calc
      ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]
        group
      _ = x * (y * T.mu 0 y' * (T.mu 0 y' * x⁻¹ * (T.mu 0 y')⁻¹) * T.mu 0 y' * y⁻¹) := by
        have hminv : (T.mu 0 y')⁻¹ = T.mu 0 y' := inv_eq_of_mul_eq_one_right hmm
        rw [show y * x⁻¹ * y⁻¹ =
          y * T.mu 0 y' * (T.mu 0 y' * x⁻¹ * (T.mu 0 y')⁻¹) * T.mu 0 y' * y⁻¹ by
            calc
              y * x⁻¹ * y⁻¹ = y * (T.mu 0 y')⁻¹ *
                    (T.mu 0 y' * x⁻¹ * (T.mu 0 y')⁻¹) * T.mu 0 y' * y⁻¹ := by group
              _ = y * T.mu 0 y' * (T.mu 0 y' * x⁻¹ * (T.mu 0 y')⁻¹) *
                    T.mu 0 y' * y⁻¹ := by rw [hminv]]
      _ = x * ((y * T.mu 0 y') * (T.mu 0 y' * x⁻¹ * (T.mu 0 y')⁻¹) *
            (T.mu 0 y' * y⁻¹)) := by group
      _ = x * ((y' * y) * X6⁻¹ * (y⁻¹ * y')) := by rw [hm1, hm2, hmxinv]
      _ = x * (y' * (y * X6⁻¹ * y⁻¹) * y') := by group
      _ = x * (y' * (X6⁻¹ * X7) * y') := by rw [hconj3inv]
      _ = x * (y' * X6⁻¹ * X7 * y'⁻¹) := by rw [hyinv]; group

  have hmirror : ⁅F.X 7 b, F.X' 0 c⁆ =
      F.X' 6 D5 * F.X 5 D4 * F.X 4 C * F.X 3 D3 * (F.X 2 (b * c))⁻¹ *
        F.X 1 (b * F.sigma c) := by
    have h0 := congrArg (MulAut.conj F.a) (F.comm_X1_X'8 b c)
    simp only [map_commutatorElement] at h0
    conv at h0 =>
      rhs
      simp only [map_mul, map_inv]
    simp only [MulAut.conj_apply] at h0
    rw [F.conj_a_X (j := 1), F.conj_a_X (j := 3), F.conj_a_X (j := 4),
      F.conj_a_X (j := 5), F.conj_a_X (j := 6), F.conj_a_X (j := 7),
      F.conj_a_X' (j := 8) (by decide), F.conj_a_X' (j := 2) (by decide)] at h0
    norm_num at h0
    have h1 := congrArg (MulAut.conj (F.rho ^ (-1 : ℤ))) h0
    simp only [map_commutatorElement] at h1
    conv at h1 =>
      rhs
      simp only [map_mul, map_inv]
    simp only [MulAut.conj_apply] at h1
    simp only [F.conj_rho_X, F.conj_rho_X'] at h1
    norm_num at h1
    rw [← hD5, ← hD4, ← hC, ← hD3] at h1
    exact h1
  have hcomm57 : ⁅y', X7⁆ = E1 * E2 * E3 * E4 * E5 * E6 := by
    rw [hyp, hX7]
    calc
      ⁅F.X' 0 c, F.X 7 b⁆ = ⁅F.X 7 b, F.X' 0 c⁆⁻¹ :=
        (commutatorElement_inv (F.X 7 b) (F.X' 0 c)).symm
      _ = (F.X' 6 D5 * F.X 5 D4 * F.X 4 C * F.X 3 D3 *
            (F.X 2 (b * c))⁻¹ * F.X 1 (b * F.sigma c))⁻¹ := by rw [hmirror]
      _ = E1 * E2 * E3 * E4 * E5 * E6 := by
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_inv_rev]
        rw [inv_inv, F.X_inv_odd (by decide : Odd (1 : ℤ)) (b * F.sigma c),
          F.X_inv_odd (by decide : Odd (3 : ℤ)) D3,
          F.X_inv_odd (by decide : Odd (5 : ℤ)) D4,
          F.X'_inv (by decide : Even (6 : ℤ)) D5]
        rw [← hE1, ← hE2, ← hE3, ← hE4, ← hE5, ← hE6]
        group
  have hcomm56 : ⁅y', X6⁆ = G1 * F2 * F1 := by
    rw [hyp, hX6]
    have h := F.r13 (-2) (by decide) c a
    norm_num at h
    rw [h, ← hG1, ← hF2, ← hF1]
  have hcomm56inv : (⁅y', X6⁆)⁻¹ = F1 * F2 * G1 := by
    rw [hcomm56, mul_inv_rev, mul_inv_rev, hF1, hF2, hG1,
      F.X'_inv (by decide : Even (4 : ℤ)) D1,
      F.X'_inv (by decide : Even (2 : ℤ)) D2,
      F.X_inv_odd (by decide : Odd (1 : ℤ)) (c * a)]
    group
  have h5 : y' * X7 * y'⁻¹ = (E1 * E2 * E3 * E4 * E5 * E6) * X7 := by
    calc
      y' * X7 * y'⁻¹ = ⁅y', X7⁆ * X7 := by
        rw [commutatorElement_def]
        group
      _ = _ := by rw [hcomm57]
  have h6 : y' * X6⁻¹ * y'⁻¹ = X6⁻¹ * F1 * F2 * G1 := by
    calc
      y' * X6⁻¹ * y'⁻¹ = X6⁻¹ * (⁅y', X6⁆)⁻¹ := by
        rw [commutatorElement_def]
        group
      _ = _ := by rw [hcomm56inv]; group

  have hQ : ⁅x, y⁆ = x * X6⁻¹ * F1 * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
    rw [h4]
    have hsplit : y' * X6⁻¹ * X7 * y'⁻¹ = (y' * X6⁻¹ * y'⁻¹) * (y' * X7 * y'⁻¹) := by
      group
    rw [hsplit, h6, h5]
    group
  have hG1E1 : G1 * E1 = 1 := by
    rw [hG1, hE1, ← hca]
    have hinv : (F.X 1 (c * a))⁻¹ = F.X 1 (c * a) := F.X_inv_odd (j := 1) (by decide) _
    calc
      F.X 1 (c * a) * F.X 1 (c * a) = F.X 1 (c * a) * (F.X 1 (c * a))⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel _
  have hF2sq : F2 * F2 = 1 := by
    rw [hF2]
    calc
      F.X' 2 D2 * F.X' 2 D2 = F.X' 2 D2 * (F.X' 2 D2)⁻¹ := by
        rw [F.X'_inv (by decide : Even (2 : ℤ)) D2]
      _ = 1 := mul_inv_cancel _
  have hE6sq : E6 * E6 = 1 := by
    rw [hE6]
    calc
      F.X' 6 D5 * F.X' 6 D5 = F.X' 6 D5 * (F.X' 6 D5)⁻¹ := by
        rw [F.X'_inv (by decide : Even (6 : ℤ)) D5]
      _ = 1 := mul_inv_cancel _
  have hF1sq : F1 * F1 = 1 := by
    rw [hF1]
    calc
      F.X' 4 D1 * F.X' 4 D1 = F.X' 4 D1 * (F.X' 4 D1)⁻¹ := by
        rw [F.X'_inv (by decide : Even (4 : ℤ)) D1]
      _ = 1 := mul_inv_cancel _
  have hE5sq : E5 * E5 = 1 := by
    rw [hE5]
    calc
      F.X 5 D4 * F.X 5 D4 = F.X 5 D4 * (F.X 5 D4)⁻¹ := by
        rw [F.X_inv_odd (j := 5) (by decide) D4]
      _ = 1 := mul_inv_cancel _
  have hxX6 : x * X6 = X6 * x := by rw [hx, hX6]; exact F.c26 0 (by decide) t a
  have hxE6 : x * E6 = E6 * x := by
    rw [hx, hE6]
    exact (T.Uprime_comm (j := 6) (k := 2) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) D5) (F.X_mem 2 t)).symm
  have hxF1 : x * F1 = F1 * x := by rw [hx, hF1]; exact F.c24' 0 (by decide) t D1
  have hxF2 : x * F2 = F2 * x := by
    rw [hx, hF2]
    exact (F.X'_comm (j := 2) (by decide) D2 t).symm
  have hxG1 : x * G1 = G1 * x := by
    rw [hx, hG1]
    exact (F.c12 0 (by decide) (c * a) t).symm
  have hxE1 : x * E1 = E1 * x := by
    rw [hx, hE1]
    exact (F.c12 0 (by decide) (b * F.sigma c) t).symm
  have hxE2 : x * E2 = F2 := by
    rw [hx, hE2, hbc, hF2, hD2t]
    exact F.X_mul_self_even (j := 2) (by decide) t
  have hE6F1 : E6 * F1 = F1 * E6 := by
    rw [hE6, hF1]
    exact (F.c2'4' 2 (by decide) D1 D5).symm
  have hE6E3 : E6 * E3 = E3 * E6 := by
    rw [hE6, hE3]
    exact T.Uprime_comm (j := 6) (k := 3) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) D5) (F.X_mem 3 D3)
  have hE6E4 : E6 * E4 = E4 * E6 := by
    rw [hE6, hE4]
    have h : F.X 4 C * E6 = E6 * F.X 4 C := by
      rw [hE6]
      exact (T.Uprime_comm (j := 6) (k := 4) (by norm_num) (by norm_num)
        (F.X'_mem (by decide) D5) (F.X_mem 4 C)).symm
    have hE6inv : E6⁻¹ = E6 := by
      rw [hE6, F.X'_inv (by decide : Even (6 : ℤ)) D5]
    calc
      E6 * (F.X 4 C)⁻¹ = (F.X 4 C * E6)⁻¹ := by
        rw [mul_inv_rev, hE6inv]
      _ = (E6 * F.X 4 C)⁻¹ := by rw [h]
      _ = (F.X 4 C)⁻¹ * E6 := by
        rw [mul_inv_rev, show E6⁻¹ = E6 from by
          rw [hE6, F.X'_inv (by decide : Even (6 : ℤ)) D5]]
  have hE6E5 : E6 * E5 = E5 * E6 := by
    rw [hE6, hE5]
    exact T.Uprime_comm (j := 6) (k := 5) (by norm_num) (by norm_num)
      (F.X'_mem (by decide) D5) (F.X_mem 5 D4)
  have hX6F1 : X6 * F1 = F1 * X6 := by
    rw [hX6, hF1]
    exact (F.c2'4 2 (by decide) D1 a).symm
  have hX6E5 : X6 * E5 = E5 * X6 := by
    rw [hX6, hE5]
    exact (F.c12 4 (by decide) D4 a).symm

  have hmoveE6 : E6 * F1 * E3 * E4 * E5 = F1 * E3 * E4 * E5 * E6 := by
    calc
      E6 * F1 * E3 * E4 * E5 = F1 * E6 * E3 * E4 * E5 := by rw [hE6F1]
      _ = F1 * (E6 * E3) * E4 * E5 := by group
      _ = F1 * (E3 * E6) * E4 * E5 := by rw [hE6E3]
      _ = F1 * E3 * (E6 * E4) * E5 := by group
      _ = F1 * E3 * (E4 * E6) * E5 := by rw [hE6E4]
      _ = F1 * E3 * E4 * (E6 * E5) := by group
      _ = F1 * E3 * E4 * (E5 * E6) := by rw [hE6E5]
      _ = F1 * E3 * E4 * E5 * E6 := by group
  have hmoveX : X6 * F1 * E3 * E4 * E5 = E3 * E4 * X6 := by
    have hX6E3 : X6 * E3 = F1 * E3 * X6 := by
      rw [hX6, hE3, hF1]
      exact X6_mul_X3_of_comm F D3 a D1 (by rw [← hD3a]; exact F.r2 2 (by decide) D3 a)
    have hX6E4 : X6 * E4 = E4 * E5 * X6 := by
      rw [hX6, hE4, hE5]
      exact X6_mul_X4_inv_of_comm F C a D4 (by rw [← hCa]; exact F.r8 2 (by decide) C a)
    calc
      X6 * F1 * E3 * E4 * E5 = F1 * X6 * E3 * E4 * E5 := by rw [hX6F1]
      _ = F1 * (X6 * E3) * E4 * E5 := by group
      _ = F1 * (F1 * E3 * X6) * E4 * E5 := by rw [hX6E3]
      _ = E3 * X6 * E4 * E5 := by
        rw [show F1 * (F1 * E3 * X6) = (F1 * F1) * (E3 * X6) by group]
        rw [hF1sq, one_mul]
      _ = E3 * (X6 * E4) * E5 := by group
      _ = E3 * (E4 * E5 * X6) * E5 := by rw [hX6E4]
      _ = E3 * E4 * E5 * X6 * E5 := by group
      _ = E3 * E4 * E5 * (X6 * E5) := by group
      _ = E3 * E4 * E5 * (E5 * X6) := by rw [hX6E5]
      _ = E3 * E4 * X6 := by
        rw [show E3 * E4 * E5 * (E5 * X6) = E3 * E4 * (E5 * E5) * X6 by group]
        rw [hE5sq, mul_one]
  have hX6inv : X6⁻¹ = X6 * E6 := by
    rw [hX6, hE6, F.X_inv_even (j := 6) (by decide) a, ← hD5sa]
  have hQ1 : x * X6⁻¹ * F1 * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 =
      X6 * E6 * F1 * E3 * E4 * E5 * E6 * X7 := by
    calc
      x * X6⁻¹ * F1 * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 =
          x * (X6 * E6) * F1 * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
        rw [hX6inv]
      _ = X6 * x * E6 * F1 * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show x * (X6 * E6) = (x * X6) * E6 by group, hxX6]
      _ = X6 * E6 * x * F1 * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * x * E6 = X6 * (x * E6) by group, hxE6]
        group
      _ = X6 * E6 * F1 * x * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * E6 * x * F1 = X6 * E6 * (x * F1) by group, hxF1]
        group
      _ = X6 * E6 * F1 * F2 * x * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * E6 * F1 * x * F2 = X6 * E6 * F1 * (x * F2) by group, hxF2]
        group
      _ = X6 * E6 * F1 * F2 * G1 * x * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * E6 * F1 * F2 * x * G1 = X6 * E6 * F1 * F2 * (x * G1) by group,
          hxG1]
        group
      _ = X6 * E6 * F1 * F2 * G1 * E1 * x * E2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * E6 * F1 * F2 * G1 * x * E1 =
          X6 * E6 * F1 * F2 * G1 * (x * E1) by group, hxE1]
        group
      _ = X6 * E6 * F1 * F2 * G1 * E1 * F2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * E6 * F1 * F2 * G1 * E1 * x * E2 =
          X6 * E6 * F1 * F2 * G1 * E1 * (x * E2) by group, hxE2]
      _ = X6 * E6 * F1 * F2 * F2 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * E6 * F1 * F2 * G1 * E1 * F2 =
          X6 * E6 * F1 * F2 * (G1 * E1) * F2 by group, hG1E1]
        group
      _ = X6 * E6 * F1 * E3 * E4 * E5 * E6 * X7 := by
        rw [show X6 * E6 * F1 * F2 * F2 * E3 =
          X6 * E6 * F1 * (F2 * F2) * E3 by group, hF2sq]
        group
  have hQ2 : X6 * E6 * F1 * E3 * E4 * E5 * E6 * X7 =
      X6 * F1 * E3 * E4 * E5 * X7 := by
    calc
      X6 * E6 * F1 * E3 * E4 * E5 * E6 * X7 =
          X6 * (E6 * F1 * E3 * E4 * E5) * E6 * X7 := by group
      _ = X6 * (F1 * E3 * E4 * E5 * E6) * E6 * X7 := by rw [hmoveE6]
      _ = X6 * F1 * E3 * E4 * E5 * X7 := by
        rw [show X6 * (F1 * E3 * E4 * E5 * E6) * E6 * X7 =
          X6 * F1 * E3 * E4 * E5 * (E6 * E6) * X7 by group, hE6sq, mul_one]
  have hQ3 : X6 * F1 * E3 * E4 * E5 * X7 = E3 * E4 * X6 * X7 := by
    calc
      X6 * F1 * E3 * E4 * E5 * X7 = (X6 * F1 * E3 * E4 * E5) * X7 := by group
      _ = (E3 * E4 * X6) * X7 := by rw [hmoveX]
      _ = E3 * E4 * X6 * X7 := by group
  calc
    ⁅F.X 2 t, F.X 8 u⁆ = x * X6⁻¹ * F1 * F2 * G1 * E1 * E2 * E3 * E4 * E5 * E6 * X7 := by
      rw [hQ]
    _ = X6 * E6 * F1 * E3 * E4 * E5 * E6 * X7 := hQ1
    _ = X6 * F1 * E3 * E4 * E5 * X7 := hQ2
    _ = E3 * E4 * X6 * X7 := hQ3
    _ = F.X 3 (F.sigma t * t * u) * (F.X 4 (F.sigma t * u))⁻¹ *
          F.X 6 (t * F.sigma u) * F.X 7 (t * F.sigma u * u) := by
      rw [hE3, hE4, hX6, hX7, hD3t, hCt, ha, hbt]

theorem r15 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (2 + s) t, F.X (8 + s) u⁆ =
      F.X (3 + s) (F.sigma t * t * u) * (F.X (4 + s) (F.sigma t * u))⁻¹ *
        F.X (6 + s) (t * F.sigma u) * F.X (7 + s) (t * F.sigma u * u) := by
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ k)) (F.comm_X2_X8 t u)
  simp only [map_commutatorElement] at h
  conv at h =>
    rhs
    simp only [map_mul, map_inv]
  simp only [MulAut.conj_apply, F.conj_rho_X, F.conj_rho_X'] at h
  rwa [show (2 : ℤ) + 2 * k = 2 + s by omega,
    show (8 : ℤ) + 2 * k = 8 + s by omega,
    show (3 : ℤ) + 2 * k = 3 + s by omega,
    show (4 : ℤ) + 2 * k = 4 + s by omega,
    show (6 : ℤ) + 2 * k = 6 + s by omega,
    show (7 : ℤ) + 2 * k = 7 + s by omega] at h

end OctFrame

noncomputable def OctFrame.toOctCoord {T : TitsSystem G 8} (F : OctFrame T) : OctCoord T.U where
  K := F.K
  σ := F.sigma
  σ_sq := F.sigma_sigma
  X := F.X
  X' := F.X'
  X_mem := F.X_mem
  X'_mem _ _ hj := T.Uprime_le _ (F.X'_mem hj _)
  X_add_odd _ hj := F.X_add_odd hj
  X'_add _ hj := F.X'_add hj
  X_mul_even _ hj := F.X_mul_even hj
  X'_comm _ hj := F.X'_comm hj
  bij_odd _ hj := F.bij_odd_X hj
  bij_even _ hj := F.bij_even_X hj
  c12 := F.c12
  c12' := F.c12'
  c13 := F.c13
  c14' := F.c14'
  c15 := F.c15
  c23 := F.c23
  c2'3 := F.c2'3
  c2'4 := F.c2'4
  c2'4' := F.c2'4'
  c24' := F.c24'
  c2'5 := F.c2'5
  c26 := F.c26
  c26' := F.c26'
  c2'6 := F.c2'6
  c2'6' := F.c2'6'
  r2 := F.r2
  r3 := F.r3
  r4 := F.r4
  r5 := F.r5
  r6 := F.r6
  r7 := F.r7
  r8 := F.r8
  r9 := F.r9
  r10 := F.r10
  r11 := F.r11
  r12 := F.r12
  r13 := F.r13
  r14 := F.r14
  r15 := F.r15

theorem exists_octCoord (T : TitsSystem G 8) (hT : T.Normalized) : Nonempty (OctCoord T.U) :=
  ⟨(Classical.choice (exists_octFrame hT)).toOctCoord⟩

end CFSG.GH74.Tits83
