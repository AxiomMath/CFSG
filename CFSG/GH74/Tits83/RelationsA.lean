module

public import CFSG.GH74.Tits83.Section4D

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

theorem two_eq_zero : (2 : F.K) = 0 := by
  have h := F.sigma_sigma 2
  rw [map_ofNat, map_ofNat] at h
  linear_combination -h

instance charP : CharP F.K 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast F.two_eq_zero)

theorem X_zero (j : ℤ) : F.X j 0 = 1 := by
  by_cases hj : Even j
  · rw [F.X_of_even hj, F.xs_zero]
  · rw [F.X_of_odd (Int.not_even_iff_odd.mp hj), F.val_zero, F.xo_one_eq]

theorem X'_zero (j : ℤ) : F.X' j 0 = 1 := by
  rw [F.X'_def, F.val_zero, F.xp_one_eq]

theorem X_ne_one (j : ℤ) {t : F.K} (ht : t ≠ 0) : F.X j t ≠ 1 := by
  by_cases hj : Even j
  · rw [F.X_of_even hj]
    exact F.xs_ne_one hj ht
  · have ho : Odd j := Int.not_even_iff_odd.mp hj
    rw [F.X_of_odd ho]
    exact F.xo_ne_one ho ht

theorem X'_ne_one {j : ℤ} (hj : Even j) {t : F.K} (ht : t ≠ 0) : F.X' j t ≠ 1 := by
  rw [F.X'_def]
  exact F.xp_ne_one_of_ne_zero hj ht

theorem X'_injective {j : ℤ} (hj : Even j) : Function.Injective (F.X' j) := by
  intro a b hab
  apply K.ext
  have h : F.xp j a.val = F.xp j b.val := by
    simpa only [F.X'_def] using hab
  exact (F.xp_bijOn hj).injOn a.mem b.mem h

theorem X_add_odd {j : ℤ} (hj : Odd j) (t u : F.K) :
    F.X j (t + u) = F.X j t * F.X j u := by
  rw [F.X_of_odd hj, F.X_of_odd hj, F.X_of_odd hj, F.val_add, F.xo_mul]

theorem X'_add {j : ℤ} (hj : Even j) (t u : F.K) :
    F.X' j (t + u) = F.X' j t * F.X' j u := by
  rw [F.X'_def, F.X'_def, F.X'_def, F.val_add]
  exact F.xp_mul t.mem u.mem j

theorem X'_comm {j : ℤ} (hj : Even j) (t u : F.K) :
    F.X' j t * F.X j u = F.X j u * F.X' j t := by
  have h := T.Uprime_comm (j := j) (k := j) (by omega) (by omega)
    (F.X'_mem hj t) (F.X_mem j u)
  simpa only [F.X'_def] using h

theorem X_inv_odd {j : ℤ} (hj : Odd j) (t : F.K) : (F.X j t)⁻¹ = F.X j t := by
  rw [F.X_of_odd hj]
  exact inv_eq_of_mul_eq_one_right (T.lemma35_i F.hT hj (F.xo_mem hj t.mem))

theorem X'_inv {j : ℤ} (hj : Even j) (t : F.K) : (F.X' j t)⁻¹ = F.X' j t := by
  rw [F.X'_def]
  exact inv_eq_of_mul_eq_one_right (T.Uprime_mul_self F.hT hj (F.xp_mem hj t.mem))

theorem conj_rho_X (k j : ℤ) (t : F.K) :
    F.rho ^ k * F.X j t * (F.rho ^ k)⁻¹ = F.X (j + 2 * k) t := by
  by_cases hj : Even j
  · by_cases ht : t = 0
    · subst ht
      rw [F.X_zero, F.X_zero]
      group
    have hj' : Even (j + 2 * k) := hj.add ⟨k, by ring⟩
    have hj8 : Even (j + 8) := hj.add (by decide)
    have hσt : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
    have hs : (F.sigma t * t)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσt ht)
    have hmem : F.X' (j + 8) ((F.sigma t * t)⁻¹) ∈ T.U (j + 8) :=
      T.Uprime_le _ (F.X'_mem hj8 _)
    have hne : F.X' (j + 8) ((F.sigma t * t)⁻¹) ≠ 1 := F.X'_ne_one hj8 hs
    have hmoves : T.Moves (F.rho ^ k) (fun i => 1 * i + 2 * k) := by
      simpa using F.moves_rho_zpow k
    have hthird := (T.mu_conj (by norm_num : 3 ≤ (8 : ℕ)) (g := F.rho ^ k) (ε := 1)
      (c := 2 * k) (Or.inl rfl) hmoves hmem hne).2.2
    simp only [one_mul] at hthird
    rw [F.X_of_even hj, F.xs_of_ne_zero ht, F.X_of_even hj', F.xs_of_ne_zero ht]
    have hxp : F.rho ^ k * F.xp (j + 8) ((F.sigma t * t)⁻¹).val * (F.rho ^ k)⁻¹ =
        F.xp (j + 2 * k + 8) ((F.sigma t * t)⁻¹).val := by
      have h := F.rho_zpow_conj_xp k (j + 8) ((F.sigma t * t)⁻¹).val
      rwa [show j + 8 + 2 * k = j + 2 * k + 8 by ring] at h
    simp only [F.X'_def] at hthird
    rw [show j + 8 + 2 * k = j + 2 * k + 8 by ring, hxp] at hthird
    exact hthird.symm
  · have ho : Odd j := Int.not_even_iff_odd.mp hj
    have ho' : Odd (j + 2 * k) := by
      obtain ⟨m, hm⟩ := ho
      exact ⟨m + k, by rw [hm]; ring⟩
    rw [F.X_of_odd ho, F.X_of_odd ho']
    exact F.rho_zpow_conj_xo k j t.val

theorem conj_rho_X' (k j : ℤ) (t : F.K) :
    F.rho ^ k * F.X' j t * (F.rho ^ k)⁻¹ = F.X' (j + 2 * k) t := by
  rw [F.X'_def, F.X'_def]
  exact F.rho_zpow_conj_xp k j t.val

theorem X_add_sixteen (j : ℤ) (t : F.K) : F.X (j + 16) t = F.X j t := by
  have h8 : F.rho ^ (8 : ℤ) = 1 := by
    rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact F.rho_pow_eight
  have h := F.conj_rho_X 8 j t
  rw [h8, one_mul, inv_one, mul_one, show j + 2 * (8 : ℤ) = j + 16 by norm_num] at h
  exact h.symm

theorem X'_add_sixteen (j : ℤ) (t : F.K) : F.X' (j + 16) t = F.X' j t := by
  have h8 : F.rho ^ (8 : ℤ) = 1 := by
    rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact F.rho_pow_eight
  have h := F.conj_rho_X' 8 j t
  rw [h8, one_mul, inv_one, mul_one, show j + 2 * (8 : ℤ) = j + 16 by norm_num] at h
  exact h.symm

theorem conj_a_X (j : ℤ) (t : F.K) : F.a * F.X j t * F.a⁻¹ = F.X (10 - j) t := by
  by_cases hj : Even j
  · have hj' : Even (10 - j) := by
      obtain ⟨m, hm⟩ := hj
      exact ⟨5 - m, by omega⟩
    rw [F.X_of_even hj, F.X_of_even hj']
    exact F.a_conj_xs hj t
  · have ho : Odd j := Int.not_even_iff_odd.mp hj
    have ho' : Odd (10 - j) := by
      obtain ⟨m, hm⟩ := ho
      exact ⟨4 - m, by rw [hm]; ring⟩
    rw [F.X_of_odd ho, F.X_of_odd ho']
    exact F.a_conj_xo ho t.mem

theorem conj_a_X' {j : ℤ} (hj : Even j) (t : F.K) :
    F.a * F.X' j t * F.a⁻¹ = F.X' (10 - j) t := by
  rw [F.X'_def, F.X'_def]
  exact F.a_conj_xp hj t.mem

theorem conj_b_X (j : ℤ) (t : F.K) : F.b * F.X j t * F.b⁻¹ = F.X (24 - j) t := by
  rw [F.b_eq]
  calc
    (F.rho⁻¹ * F.a) * F.X j t * (F.rho⁻¹ * F.a)⁻¹
        = F.rho⁻¹ * (F.a * F.X j t * F.a⁻¹) * (F.rho⁻¹)⁻¹ := by group
    _ = F.rho⁻¹ * F.X (10 - j) t * (F.rho⁻¹)⁻¹ := by rw [F.conj_a_X]
    _ = F.X (10 - j + 2 * (-1)) t := by
      simpa using F.conj_rho_X (-1) (10 - j) t
    _ = F.X (24 - j) t := by
      rw [show 10 - j + 2 * (-1) = 8 - j by ring,
        show 24 - j = (8 - j) + 16 by ring, F.X_add_sixteen]

theorem conj_b_X' {j : ℤ} (hj : Even j) (t : F.K) :
    F.b * F.X' j t * F.b⁻¹ = F.X' (24 - j) t := by
  rw [F.b_eq]
  calc
    (F.rho⁻¹ * F.a) * F.X' j t * (F.rho⁻¹ * F.a)⁻¹
        = F.rho⁻¹ * (F.a * F.X' j t * F.a⁻¹) * (F.rho⁻¹)⁻¹ := by group
    _ = F.rho⁻¹ * F.X' (10 - j) t * (F.rho⁻¹)⁻¹ := by rw [F.conj_a_X' hj]
    _ = F.X' (10 - j + 2 * (-1)) t := by
      simpa using F.conj_rho_X' (-1) (10 - j) t
    _ = F.X' (24 - j) t := by
      rw [show 10 - j + 2 * (-1) = 8 - j by ring,
        show 24 - j = (8 - j) + 16 by ring, F.X'_add_sixteen]

@[expose] noncomputable def wtX (x : F.K) (j : ℤ) : F.K :=
  if j % 16 = 1 then x ^ 2
  else if j % 16 = 3 ∨ j % 16 = 15 then F.sigma x
  else if j % 16 = 5 ∨ j % 16 = 13 then 1
  else if j % 16 = 7 ∨ j % 16 = 11 then (F.sigma x)⁻¹
  else if j % 16 = 9 then (x ^ 2)⁻¹
  else if j % 16 = 0 ∨ j % 16 = 2 then x
  else if j % 16 = 4 ∨ j % 16 = 14 then F.sigma x / x
  else if j % 16 = 6 ∨ j % 16 = 12 then x / F.sigma x
  else x⁻¹

@[expose] noncomputable def wtX' (x : F.K) (j : ℤ) : F.K :=
  if j % 16 = 0 ∨ j % 16 = 2 then F.sigma x * x
  else if j % 16 = 4 ∨ j % 16 = 14 then x
  else if j % 16 = 6 ∨ j % 16 = 12 then x⁻¹
  else (F.sigma x * x)⁻¹

theorem wtX_two_sub (x : F.K) (j : ℤ) : F.wtX x (2 - j) = F.wtX x j := by
  have h0 := Int.emod_nonneg j (by norm_num : (16 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 16)
  interval_cases h : j % 16 <;>
    simp [wtX, Int.sub_emod, Int.add_mul_emod_self_right, h]
theorem wtX'_two_sub (x : F.K) (j : ℤ) : F.wtX' x (2 - j) = F.wtX' x j := by
  have h0 := Int.emod_nonneg j (by norm_num : (16 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 16)
  interval_cases h : j % 16 <;>
    simp [wtX', Int.sub_emod, Int.add_mul_emod_self_right, h]
theorem wtX_ne_zero {x : F.K} (hx : x ≠ 0) (j : ℤ) : F.wtX x j ≠ 0 := by
  have hσ : F.sigma x ≠ 0 := (map_ne_zero F.sigma).2 hx
  have h0 := Int.emod_nonneg j (by norm_num : (16 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 16)
  interval_cases h : j % 16 <;>
    simp [wtX, h, hx, hσ, pow_ne_zero, inv_ne_zero, div_ne_zero, mul_ne_zero]
theorem wtX'_ne_zero {x : F.K} (hx : x ≠ 0) (j : ℤ) : F.wtX' x j ≠ 0 := by
  have hσ : F.sigma x ≠ 0 := (map_ne_zero F.sigma).2 hx
  have h0 := Int.emod_nonneg j (by norm_num : (16 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 16)
  interval_cases h : j % 16 <;>
    simp [wtX', h, hx, hσ, pow_ne_zero, inv_ne_zero, div_ne_zero, mul_ne_zero]
theorem sigma_wtX_mul {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Even j) :
    F.sigma (F.wtX x j) * F.wtX x j = (F.wtX' x (j + 8))⁻¹ := by
  have hσ : F.sigma x ≠ 0 := (map_ne_zero F.sigma).2 hx
  obtain ⟨m, hm⟩ := hj
  rw [hm]
  have hmod : (m + m) % 16 = 0 ∨ (m + m) % 16 = 2 ∨ (m + m) % 16 = 4 ∨
      (m + m) % 16 = 6 ∨ (m + m) % 16 = 8 ∨ (m + m) % 16 = 10 ∨
      (m + m) % 16 = 12 ∨ (m + m) % 16 = 14 := by
    have h0 := Int.emod_nonneg (m + m) (by norm_num : (16 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos (m + m) (by norm_num : (0 : ℤ) < 16)
    omega
  have h8 : (m + m + 8) % 16 = ((m + m) % 16 + 8) % 16 := by
    rw [Int.add_emod]
    norm_num
  rcases hmod with h | h | h | h | h | h | h | h <;>
    simp [wtX, wtX', h, h8, hσ, hx, F.sigma_sigma, pow_ne_zero, inv_inv,
      div_eq_mul_inv, map_mul, map_div₀, map_inv₀] <;>
    field_simp <;> ring

private theorem xo_add_mul_sixteen (k j : ℤ) (x : G) : F.xo (j + 16 * k) x = F.xo j x := by
  have h8 : F.rho ^ (8 : ℤ) = 1 := by
    rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact F.rho_pow_eight
  have h := F.rho_zpow_conj_xo (8 * k) j x
  rw [show (8 * k : ℤ) = (8 : ℤ) * k by ring, zpow_mul, h8, one_zpow] at h
  rw [show j + 2 * (8 * k) = j + 16 * k by ring] at h
  simpa using h.symm

private theorem xp_add_mul_sixteen (k j : ℤ) (x : G) : F.xp (j + 16 * k) x = F.xp j x := by
  have h8 : F.rho ^ (8 : ℤ) = 1 := by
    rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact F.rho_pow_eight
  have h := F.rho_zpow_conj_xp (8 * k) j x
  rw [show (8 * k : ℤ) = (8 : ℤ) * k by ring, zpow_mul, h8, one_zpow] at h
  rw [show j + 2 * (8 * k) = j + 16 * k by ring] at h
  simpa using h.symm

private theorem X'_eq_of_emod {j r : ℤ} (h : j % 16 = r % 16) (v : F.K) :
    F.X' j v = F.X' r v := by
  have hd := (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hd
  have hj : j = r + 16 * k := by omega
  rw [hj, F.X'_def, F.xp_add_mul_sixteen k r v.val, ← F.X'_def]

private theorem X_eq_of_emod_odd {j r : ℤ} (h : j % 16 = r % 16) (hr : Odd r) (v : F.K) :
    F.X j v = F.X r v := by
  have hd := (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hd
  have hj : j = r + 16 * k := by omega
  have hj' : Odd (r + 16 * k) := by
    obtain ⟨m, hm⟩ := hr
    exact ⟨m + 8 * k, by rw [hm]; ring⟩
  rw [hj, F.X_of_odd hj', F.X_of_odd hr, F.xo_add_mul_sixteen k r v.val]

private theorem wtX_eq_of_emod (x : F.K) {j r : ℤ} (h : j % 16 = r % 16) :
    F.wtX x j = F.wtX x r := by
  have hd := (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hd
  rw [show j = r + 16 * k by omega]
  simp [wtX, Int.add_mul_emod_self_right]

private theorem wtX'_eq_of_emod (x : F.K) {j r : ℤ} (h : j % 16 = r % 16) :
    F.wtX' x j = F.wtX' x r := by
  have hd := (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hd
  rw [show j = r + 16 * k by omega]
  simp [wtX', Int.add_mul_emod_self_right]

private theorem alpha_conj_X'_two {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 2 v * (F.alpha x)⁻¹ = F.X' 2 (F.wtX' x 2 * v) := by
  rw [F.X'_def, F.X'_def]
  simp only [wtX']
  norm_num
  exact F.alpha_xp_two hx v

private theorem alpha_conj_X'_four {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 4 v * (F.alpha x)⁻¹ = F.X' 4 (F.wtX' x 4 * v) := by
  rw [F.X'_def, F.X'_def]
  simp only [wtX']
  norm_num
  exact F.alpha_xp_four' hx v

private theorem alpha_conj_X'_six {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 6 v * (F.alpha x)⁻¹ = F.X' 6 (F.wtX' x 6 * v) := by
  rw [F.X'_def, F.X'_def]
  simp only [wtX']
  norm_num
  exact F.alpha_xp_six hx v

private theorem alpha_conj_X'_eight {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 8 v * (F.alpha x)⁻¹ = F.X' 8 (F.wtX' x 8 * v) := by
  rw [F.X'_def, F.X'_def]
  simp only [wtX']
  norm_num
  have harg : x⁻¹ * (F.sigma x)⁻¹ * v = (F.sigma x * x)⁻¹ * v := by
    rw [mul_inv_rev]
  rw [harg]
  exact F.alpha_xp_eight hx v

private theorem alpha_conj_X'_of_refl {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Even j) (v : F.K)
    (h : F.alpha x * F.X' j v * (F.alpha x)⁻¹ = F.X' j (F.wtX' x j * v)) :
    F.alpha x * F.X' (2 - j) v * (F.alpha x)⁻¹ =
      F.X' (2 - j) (F.wtX' x (2 - j) * v) := by
  let r : G := F.rho ^ (-4 : ℤ) * F.a
  have hrx : r * F.X' j v * r⁻¹ = F.X' (2 - j) v := by
    rw [F.X'_def, F.X'_def]
    have h := F.rho_zpow_a_conj_xp (-4) hj v.mem
    rwa [show (10 : ℤ) + 2 * (-4) - j = 2 - j by ring] at h
  have hrxw : r * F.X' j (F.wtX' x j * v) * r⁻¹ = F.X' (2 - j) (F.wtX' x j * v) := by
    rw [F.X'_def, F.X'_def]
    have h := F.rho_zpow_a_conj_xp (-4) hj (F.wtX' x j * v).mem
    rwa [show (10 : ℤ) + 2 * (-4) - j = 2 - j by ring] at h
  have hαr : F.alpha x * r = r * F.alpha x := F.alpha_comm_refl hx
  have hαrinv : r⁻¹ * (F.alpha x)⁻¹ = (F.alpha x)⁻¹ * r⁻¹ := by
    simpa [mul_inv_rev] using congrArg Inv.inv hαr
  calc
    F.alpha x * F.X' (2 - j) v * (F.alpha x)⁻¹
        = F.alpha x * (r * F.X' j v * r⁻¹) * (F.alpha x)⁻¹ := by rw [hrx]
    _ = r * (F.alpha x * F.X' j v * (F.alpha x)⁻¹) * r⁻¹ := by
      calc
        F.alpha x * (r * F.X' j v * r⁻¹) * (F.alpha x)⁻¹
            = (F.alpha x * r) * F.X' j v * (r⁻¹ * (F.alpha x)⁻¹) := by group
        _ = (r * F.alpha x) * F.X' j v * ((F.alpha x)⁻¹ * r⁻¹) := by rw [hαr, hαrinv]
        _ = r * (F.alpha x * F.X' j v * (F.alpha x)⁻¹) * r⁻¹ := by group
    _ = r * F.X' j (F.wtX' x j * v) * r⁻¹ := by rw [h]
    _ = F.X' (2 - j) (F.wtX' x j * v) := hrxw
    _ = F.X' (2 - j) (F.wtX' x (2 - j) * v) := by rw [F.wtX'_two_sub x j]

private theorem alpha_conj_X'_zero {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 0 v * (F.alpha x)⁻¹ = F.X' 0 (F.wtX' x 0 * v) := by
  have h := F.alpha_conj_X'_of_refl hx (j := 2) (by decide) v (F.alpha_conj_X'_two hx v)
  simpa using h

private theorem alpha_conj_X'_ten {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 10 v * (F.alpha x)⁻¹ = F.X' 10 (F.wtX' x 10 * v) := by
  have h := F.alpha_conj_X'_of_refl hx (j := 8) (by decide) v (F.alpha_conj_X'_eight hx v)
  have hX : F.X' (2 - 8) v = F.X' 10 v := F.X'_eq_of_emod (by norm_num) v
  have hw : F.wtX' x (2 - 8) = F.wtX' x 10 := F.wtX'_eq_of_emod x (by norm_num)
  have hXw : F.X' (2 - 8) (F.wtX' x (2 - 8) * v) = F.X' 10 (F.wtX' x 10 * v) := by
    rw [hw]
    exact F.X'_eq_of_emod (by norm_num) (F.wtX' x 10 * v)
  rw [hX, hXw] at h
  exact h

private theorem alpha_conj_X'_twelve {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 12 v * (F.alpha x)⁻¹ = F.X' 12 (F.wtX' x 12 * v) := by
  have h := F.alpha_conj_X'_of_refl hx (j := 6) (by decide) v (F.alpha_conj_X'_six hx v)
  have hX : F.X' (2 - 6) v = F.X' 12 v := F.X'_eq_of_emod (by norm_num) v
  have hw : F.wtX' x (2 - 6) = F.wtX' x 12 := F.wtX'_eq_of_emod x (by norm_num)
  have hXw : F.X' (2 - 6) (F.wtX' x (2 - 6) * v) = F.X' 12 (F.wtX' x 12 * v) := by
    rw [hw]
    exact F.X'_eq_of_emod (by norm_num) (F.wtX' x 12 * v)
  rw [hX, hXw] at h
  exact h

private theorem alpha_conj_X'_fourteen {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X' 14 v * (F.alpha x)⁻¹ = F.X' 14 (F.wtX' x 14 * v) := by
  have h := F.alpha_conj_X'_of_refl hx (j := 4) (by decide) v (F.alpha_conj_X'_four hx v)
  have hX : F.X' (2 - 4) v = F.X' 14 v := F.X'_eq_of_emod (by norm_num) v
  have hw : F.wtX' x (2 - 4) = F.wtX' x 14 := F.wtX'_eq_of_emod x (by norm_num)
  have hXw : F.X' (2 - 4) (F.wtX' x (2 - 4) * v) = F.X' 14 (F.wtX' x 14 * v) := by
    rw [hw]
    exact F.X'_eq_of_emod (by norm_num) (F.wtX' x 14 * v)
  rw [hX, hXw] at h
  exact h

private theorem alpha_conj_X_one {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 1 v * (F.alpha x)⁻¹ = F.X 1 (F.wtX x 1 * v) := by
  rw [F.X_of_odd (by decide), F.X_of_odd (by decide)]
  simp only [wtX]
  norm_num
  exact F.alpha_xo_one hx v

private theorem alpha_conj_X_three {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 3 v * (F.alpha x)⁻¹ = F.X 3 (F.wtX x 3 * v) := by
  rw [F.X_of_odd (by decide), F.X_of_odd (by decide)]
  simp only [wtX]
  norm_num
  exact F.alpha_xo_three hx v

private theorem alpha_conj_X_five {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 5 v * (F.alpha x)⁻¹ = F.X 5 (F.wtX x 5 * v) := by
  rw [F.X_of_odd (by decide), F.X_of_odd (by decide)]
  simp only [wtX]
  norm_num
  exact F.alpha_xo_five hx v

private theorem alpha_conj_X_seven {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 7 v * (F.alpha x)⁻¹ = F.X 7 (F.wtX x 7 * v) := by
  rw [F.X_of_odd (by decide), F.X_of_odd (by decide)]
  simp only [wtX]
  norm_num
  exact F.alpha_xo_seven hx v

private theorem alpha_conj_X_nine {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 9 v * (F.alpha x)⁻¹ = F.X 9 (F.wtX x 9 * v) := by
  rw [F.X_of_odd (by decide), F.X_of_odd (by decide)]
  simp only [wtX]
  norm_num
  exact F.alpha_xo_nine hx v

private theorem alpha_conj_X_of_refl {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Odd j) (v : F.K)
    (h : F.alpha x * F.X j v * (F.alpha x)⁻¹ = F.X j (F.wtX x j * v)) :
    F.alpha x * F.X (2 - j) v * (F.alpha x)⁻¹ =
      F.X (2 - j) (F.wtX x (2 - j) * v) := by
  let r : G := F.rho ^ (-4 : ℤ) * F.a
  have hj' : Odd (2 - j) := by
    obtain ⟨m, hm⟩ := hj
    exact ⟨-m, by rw [hm]; ring⟩
  have hrx : r * F.X j v * r⁻¹ = F.X (2 - j) v := by
    rw [F.X_of_odd hj, F.X_of_odd hj']
    have h := F.rho_zpow_a_conj_xo (-4) hj v.mem
    rwa [show (10 : ℤ) + 2 * (-4) - j = 2 - j by ring] at h
  have hrxw : r * F.X j (F.wtX x j * v) * r⁻¹ = F.X (2 - j) (F.wtX x j * v) := by
    rw [F.X_of_odd hj, F.X_of_odd hj']
    have h := F.rho_zpow_a_conj_xo (-4) hj (F.wtX x j * v).mem
    rwa [show (10 : ℤ) + 2 * (-4) - j = 2 - j by ring] at h
  have hαr : F.alpha x * r = r * F.alpha x := F.alpha_comm_refl hx
  have hαrinv : r⁻¹ * (F.alpha x)⁻¹ = (F.alpha x)⁻¹ * r⁻¹ := by
    simpa [mul_inv_rev] using congrArg Inv.inv hαr
  calc
    F.alpha x * F.X (2 - j) v * (F.alpha x)⁻¹
        = F.alpha x * (r * F.X j v * r⁻¹) * (F.alpha x)⁻¹ := by rw [hrx]
    _ = r * (F.alpha x * F.X j v * (F.alpha x)⁻¹) * r⁻¹ := by
      calc
        F.alpha x * (r * F.X j v * r⁻¹) * (F.alpha x)⁻¹
            = (F.alpha x * r) * F.X j v * (r⁻¹ * (F.alpha x)⁻¹) := by group
        _ = (r * F.alpha x) * F.X j v * ((F.alpha x)⁻¹ * r⁻¹) := by rw [hαr, hαrinv]
        _ = r * (F.alpha x * F.X j v * (F.alpha x)⁻¹) * r⁻¹ := by group
    _ = r * F.X j (F.wtX x j * v) * r⁻¹ := by rw [h]
    _ = F.X (2 - j) (F.wtX x j * v) := hrxw
    _ = F.X (2 - j) (F.wtX x (2 - j) * v) := by rw [F.wtX_two_sub x j]

private theorem alpha_conj_X_eleven {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 11 v * (F.alpha x)⁻¹ = F.X 11 (F.wtX x 11 * v) := by
  have h := F.alpha_conj_X_of_refl hx (j := 7) (by decide) v (F.alpha_conj_X_seven hx v)
  have hX : F.X (2 - 7) v = F.X 11 v := F.X_eq_of_emod_odd (by norm_num) (by decide) v
  have hw : F.wtX x (2 - 7) = F.wtX x 11 := F.wtX_eq_of_emod x (by norm_num)
  have hXw : F.X (2 - 7) (F.wtX x (2 - 7) * v) = F.X 11 (F.wtX x 11 * v) := by
    rw [hw]
    exact F.X_eq_of_emod_odd (by norm_num) (by decide) (F.wtX x 11 * v)
  rw [hX, hXw] at h
  exact h

private theorem alpha_conj_X_thirteen {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 13 v * (F.alpha x)⁻¹ = F.X 13 (F.wtX x 13 * v) := by
  have h := F.alpha_conj_X_of_refl hx (j := 5) (by decide) v (F.alpha_conj_X_five hx v)
  have hX : F.X (2 - 5) v = F.X 13 v := F.X_eq_of_emod_odd (by norm_num) (by decide) v
  have hw : F.wtX x (2 - 5) = F.wtX x 13 := F.wtX_eq_of_emod x (by norm_num)
  have hXw : F.X (2 - 5) (F.wtX x (2 - 5) * v) = F.X 13 (F.wtX x 13 * v) := by
    rw [hw]
    exact F.X_eq_of_emod_odd (by norm_num) (by decide) (F.wtX x 13 * v)
  rw [hX, hXw] at h
  exact h

private theorem alpha_conj_X_fifteen {x : F.K} (hx : x ≠ 0) (v : F.K) :
    F.alpha x * F.X 15 v * (F.alpha x)⁻¹ = F.X 15 (F.wtX x 15 * v) := by
  have h := F.alpha_conj_X_of_refl hx (j := 3) (by decide) v (F.alpha_conj_X_three hx v)
  have hX : F.X (2 - 3) v = F.X 15 v := F.X_eq_of_emod_odd (by norm_num) (by decide) v
  have hw : F.wtX x (2 - 3) = F.wtX x 15 := F.wtX_eq_of_emod x (by norm_num)
  have hXw : F.X (2 - 3) (F.wtX x (2 - 3) * v) = F.X 15 (F.wtX x 15 * v) := by
    rw [hw]
    exact F.X_eq_of_emod_odd (by norm_num) (by decide) (F.wtX x 15 * v)
  rw [hX, hXw] at h
  exact h

private theorem alpha_conj_X_of_emod_odd {x : F.K} (hx : x ≠ 0) {j r : ℤ}
    (h : j % 16 = r % 16) (hr : Odd r) (v : F.K)
    (hbase : F.alpha x * F.X r v * (F.alpha x)⁻¹ = F.X r (F.wtX x r * v)) :
    F.alpha x * F.X j v * (F.alpha x)⁻¹ = F.X j (F.wtX x j * v) := by
  have hX : F.X j v = F.X r v := F.X_eq_of_emod_odd h hr v
  have hw : F.wtX x j = F.wtX x r := F.wtX_eq_of_emod x h
  have hXw : F.X j (F.wtX x j * v) = F.X r (F.wtX x r * v) := by
    rw [hw]
    exact F.X_eq_of_emod_odd h hr (F.wtX x r * v)
  rw [hX, hXw]
  exact hbase

private theorem alpha_conj_X'_of_emod {x : F.K} (hx : x ≠ 0) {j r : ℤ}
    (h : j % 16 = r % 16) (v : F.K)
    (hbase : F.alpha x * F.X' r v * (F.alpha x)⁻¹ = F.X' r (F.wtX' x r * v)) :
    F.alpha x * F.X' j v * (F.alpha x)⁻¹ = F.X' j (F.wtX' x j * v) := by
  have hX : F.X' j v = F.X' r v := F.X'_eq_of_emod h v
  have hw : F.wtX' x j = F.wtX' x r := F.wtX'_eq_of_emod x h
  have hXw : F.X' j (F.wtX' x j * v) = F.X' r (F.wtX' x r * v) := by
    rw [hw]
    exact F.X'_eq_of_emod h (F.wtX' x r * v)
  rw [hX, hXw]
  exact hbase

theorem alpha_conj_X' {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Even j) (v : F.K) :
    F.alpha x * F.X' j v * (F.alpha x)⁻¹ = F.X' j (F.wtX' x j * v) := by
  have hcases : j % 16 = 0 ∨ j % 16 = 2 ∨ j % 16 = 4 ∨ j % 16 = 6 ∨
      j % 16 = 8 ∨ j % 16 = 10 ∨ j % 16 = 12 ∨ j % 16 = 14 := by
    have h0 := Int.emod_nonneg j (by norm_num : (16 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 16)
    obtain ⟨m, hm⟩ := hj
    omega
  rcases hcases with h | h | h | h | h | h | h | h
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_zero hx v)
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_two hx v)
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_four hx v)
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_six hx v)
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_eight hx v)
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_ten hx v)
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_twelve hx v)
  · exact F.alpha_conj_X'_of_emod hx (by simpa using h) v (F.alpha_conj_X'_fourteen hx v)

private theorem alpha_conj_X_even {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Even j) (v : F.K) :
    F.alpha x * F.X j v * (F.alpha x)⁻¹ = F.X j (F.wtX x j * v) := by
  by_cases hv : v = 0
  · subst hv
    rw [mul_zero, F.X_zero]
    group
  have hσv : F.sigma v ≠ 0 := (map_ne_zero F.sigma).2 hv
  have hs : (F.sigma v * v)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσv hv)
  have hw : F.wtX x j ≠ 0 := F.wtX_ne_zero hx j
  have hwv : F.wtX x j * v ≠ 0 := mul_ne_zero hw hv
  have hj8 : Even (j + 8) := hj.add (by decide)
  have hmem : F.X' (j + 8) ((F.sigma v * v)⁻¹) ∈ T.U (j + 8) :=
    T.Uprime_le _ (F.X'_mem hj8 _)
  have hne : F.X' (j + 8) ((F.sigma v * v)⁻¹) ≠ 1 := F.X'_ne_one hj8 hs
  have hαne : x.val ≠ 1 := by
    intro h
    exact hx (F.val_eq_one_iff.mp h)
  have hmoves : T.Moves (F.alpha x) (fun i => 1 * i + 0) := by
    simpa using F.moves_alpha hαne
  have hthird := (T.mu_conj (by norm_num : 3 ≤ (8 : ℕ)) (g := F.alpha x) (ε := 1)
    (c := 0) (Or.inl rfl) hmoves hmem hne).2.2
  simp only [one_mul, add_zero] at hthird
  rw [F.alpha_conj_X' hx hj8 ((F.sigma v * v)⁻¹)] at hthird
  rw [F.X'_def] at hthird
  rw [F.X_of_even hj, F.xs_of_ne_zero hv, F.X_of_even hj, F.xs_of_ne_zero hwv]
  have hs' : (F.sigma (F.wtX x j * v) * (F.wtX x j * v))⁻¹ =
      F.wtX' x (j + 8) * (F.sigma v * v)⁻¹ := by
    have hsw : F.sigma (F.wtX x j) * F.wtX x j = (F.wtX' x (j + 8))⁻¹ :=
      F.sigma_wtX_mul hx hj
    calc
      (F.sigma (F.wtX x j * v) * (F.wtX x j * v))⁻¹
          = ((F.sigma (F.wtX x j) * F.wtX x j) * (F.sigma v * v))⁻¹ := by
              rw [map_mul]; ring
      _ = (F.sigma (F.wtX x j) * F.wtX x j)⁻¹ * (F.sigma v * v)⁻¹ := mul_inv _ _
      _ = F.wtX' x (j + 8) * (F.sigma v * v)⁻¹ := by rw [hsw, inv_inv]
  rw [hs']
  exact hthird.symm

theorem alpha_conj_X {x : F.K} (hx : x ≠ 0) (j : ℤ) (v : F.K) :
    F.alpha x * F.X j v * (F.alpha x)⁻¹ = F.X j (F.wtX x j * v) := by
  by_cases hj : Even j
  · exact F.alpha_conj_X_even hx hj v
  · have hcases : j % 16 = 1 ∨ j % 16 = 3 ∨ j % 16 = 5 ∨ j % 16 = 7 ∨
        j % 16 = 9 ∨ j % 16 = 11 ∨ j % 16 = 13 ∨ j % 16 = 15 := by
      have h0 := Int.emod_nonneg j (by norm_num : (16 : ℤ) ≠ 0)
      have h1 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 16)
      obtain ⟨m, hm⟩ := Int.not_even_iff_odd.mp hj
      omega
    rcases hcases with h | h | h | h | h | h | h | h
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_one hx v)
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_three hx v)
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_five hx v)
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_seven hx v)
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_nine hx v)
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_eleven hx v)
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_thirteen hx v)
    · exact F.alpha_conj_X_of_emod_odd hx (by simpa using h) (by decide) v
        (F.alpha_conj_X_fifteen hx v)

end OctFrame

end CFSG.GH74.Tits83
