module

public import CFSG.GH74.Tits83.RelationsA

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

theorem mu_X_one {t : F.K} (ht : t ≠ 0) : T.mu 1 (F.X 1 t) = F.alpha t * F.a := by
  rw [show F.X 1 t = t.val by rw [F.X_of_odd (by decide), F.xo_one]]
  rw [show F.alpha t = T.mu 1 t.val * F.a from rfl, mul_assoc, F.a_mul_self, mul_one]

theorem mu_X_odd {i : ℤ} (hi : Odd i) {t : F.K} (ht : t ≠ 0) :
    T.mu i (F.X i t) =
      F.rho ^ ((i - 1) / 2) * (F.alpha t * F.a) * (F.rho ^ ((i - 1) / 2))⁻¹ := by
  obtain ⟨k, hk⟩ := hi
  subst hk
  rw [show (2 * k + 1 : ℤ) = 1 + 2 * k by ring]
  have hX : F.X (1 + 2 * k) t = F.rho ^ k * F.X 1 t * (F.rho ^ k)⁻¹ := by
    simpa using (F.conj_rho_X k 1 t).symm
  have hmoves : T.Moves (F.rho ^ k) (fun j : ℤ => (1 : ℤ) * j + 2 * k) := by
    simpa using F.moves_rho_zpow k
  have h := (T.mu_conj (by norm_num : 3 ≤ 8) (g := F.rho ^ k) (ε := 1) (c := 2 * k)
    (Or.inl rfl) hmoves (i := 1) (u := F.X 1 t) (F.X_mem 1 t) (F.X_ne_one 1 ht)).1
  rw [one_mul] at h
  rw [hX, h, F.mu_X_one ht]
  have hkdiv : (1 + 2 * k - 1) / 2 = k := by
    rw [show 1 + 2 * k - 1 = k * 2 by ring]
    exact Int.mul_ediv_cancel k (b := 2) (by norm_num)
  rw [hkdiv]

theorem mu_e4 : T.mu 4 (F.X' 4 1) = F.rho ^ (-4 : ℤ) * F.b := by
  have hX : F.X' 4 (1 : F.K) = F.rho ^ (-2 : ℤ) * F.e8 * (F.rho ^ (-2 : ℤ))⁻¹ := by
    rw [F.X'_def, F.val_one, F.xp_four, F.comm_e1_e6,
      show (F.rho ^ (-2 : ℤ))⁻¹ = F.rho ^ (2 : ℤ) by
        rw [← zpow_neg]
        norm_num]
  rw [hX]
  have hmoves : T.Moves (F.rho ^ (-2 : ℤ)) (fun j : ℤ => (1 : ℤ) * j + (-4)) := by
    simpa using F.moves_rho_zpow (-2 : ℤ)
  have h := (T.mu_conj (by norm_num : 3 ≤ 8) (g := F.rho ^ (-2 : ℤ)) (ε := 1)
    (c := -4) (Or.inl rfl) hmoves (i := 8) (u := F.e8)
    (T.Uprime_le 8 F.e8_mem) F.e8_ne).1
  rw [show (1 : ℤ) * 8 + (-4) = 4 by norm_num] at h
  rw [h, show T.mu 8 F.e8 = F.b from rfl]
  rw [show (F.rho ^ (-2 : ℤ))⁻¹ = F.rho ^ (2 : ℤ) by
    rw [← zpow_neg]
    norm_num]
  calc
    F.rho ^ (-2 : ℤ) * F.b * F.rho ^ (2 : ℤ) =
        F.rho ^ (-2 : ℤ) * (F.b * F.rho ^ (2 : ℤ)) := by rw [mul_assoc]
    _ = F.rho ^ (-2 : ℤ) * (F.rho ^ (-2 : ℤ) * F.b) := by rw [F.b_mul_rho_zpow]
    _ = (F.rho ^ (-2 : ℤ) * F.rho ^ (-2 : ℤ)) * F.b := by rw [mul_assoc]
    _ = F.rho ^ (-4 : ℤ) * F.b := by
        rw [← zpow_add]
        norm_num

theorem mu_X'_four {t : F.K} (ht : t ≠ 0) :
    T.mu 4 (F.X' 4 t) = F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹ := by
  have hX : F.X' 4 t = F.alpha t * F.X' 4 (1 : F.K) * (F.alpha t)⁻¹ := by
    have h := F.alpha_conj_X' (j := 4) ht (by decide : Even (4 : ℤ)) (1 : F.K)
    rw [show F.wtX' t 4 = t by simp only [OctFrame.wtX']; norm_num, mul_one] at h
    exact h.symm
  rw [hX]
  have hmoves : T.Moves (F.alpha t) (fun j : ℤ => (1 : ℤ) * j + 0) := by
    simpa using F.moves_alpha (F.val_ne_one ht)
  have h := (T.mu_conj (by norm_num : 3 ≤ 8) (g := F.alpha t) (ε := 1) (c := 0)
    (Or.inl rfl) hmoves (i := 4) (u := F.X' 4 (1 : F.K))
    (T.Uprime_le 4 (F.X'_mem (by decide) 1)) (F.X'_ne_one (by decide) one_ne_zero)).1
  rw [show (1 : ℤ) * 4 + 0 = 4 by norm_num] at h
  rw [h, F.mu_e4]

theorem mu_X'_even {i : ℤ} (hi : Even i) {t : F.K} (ht : t ≠ 0) :
    T.mu i (F.X' i t) =
      F.rho ^ ((i - 4) / 2) * T.mu 4 (F.X' 4 t) * (F.rho ^ ((i - 4) / 2))⁻¹ := by
  obtain ⟨k, hk⟩ := hi
  subst hk
  have hki : (k + k - 4) / 2 = k - 2 := by omega
  rw [hki]
  have hX : F.X' (k + k) t = F.rho ^ (k - 2) * F.X' 4 t * (F.rho ^ (k - 2))⁻¹ := by
    have h := F.conj_rho_X' (k - 2) 4 t
    rw [show (4 : ℤ) + 2 * (k - 2) = k + k by ring] at h
    exact h.symm
  rw [hX]
  have hmoves : T.Moves (F.rho ^ (k - 2)) (fun j : ℤ => (1 : ℤ) * j + 2 * (k - 2)) := by
    simpa using F.moves_rho_zpow (k - 2)
  have h := (T.mu_conj (by norm_num : 3 ≤ 8) (g := F.rho ^ (k - 2)) (ε := 1)
    (c := 2 * (k - 2)) (Or.inl rfl) hmoves (i := 4) (u := F.X' 4 t)
    (T.Uprime_le 4 (F.X'_mem (by decide) t))
    (F.X'_ne_one (by decide) ht)).1
  rw [show (1 : ℤ) * 4 + 2 * (k - 2) = k + k by ring] at h
  rw [← h]

theorem mu_X_even {i : ℤ} (hi : Even i) {t : F.K} (ht : t ≠ 0) :
    T.mu i (F.X i t) = T.mu (i + 8) (F.X' (i + 8) (F.sigma t * t)⁻¹) := by
  have hσt : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  have harg : (F.sigma t * t)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσt ht)
  have hi8 : Even (i + 8) := hi.add (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
  have hXs : F.X i t = T.nu' (i + 8) (F.X' (i + 8) (F.sigma t * t)⁻¹) := by
    rw [F.X_of_even hi, F.xs_of_ne_zero ht, F.X'_def]
  rw [hXs]
  have h := (T.mu_nu' (by norm_num : 3 ≤ 8) (i := i + 8)
    (u := F.X' (i + 8) (F.sigma t * t)⁻¹)
    (T.Uprime_le (i + 8) (F.X'_mem hi8 _))
    (F.X'_ne_one hi8 harg)).1
  rw [show i + 8 + ((8 : ℕ) : ℤ) = i + 16 by ring] at h
  rw [← h]
  rw [← T.mu_add_two_mul (by norm_num : 3 ≤ 8) (i := i) (k := 1)
    (u := T.nu' (i + 8) (F.X' (i + 8) (F.sigma t * t)⁻¹))]
  rfl

theorem mu_X_mul_self (i : ℤ) {t : F.K} (ht : t ≠ 0) :
    T.mu i (F.X i t) * T.mu i (F.X i t) = 1 := by
  by_cases hi : Even i
  · have hσt : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
    have harg : (F.sigma t * t)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσt ht)
    have hi8 : Even (i + 8) := hi.add (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
    rw [F.mu_X_even hi ht]
    exact T.mu_mul_self_Uprime F.hT hi8 (F.X'_mem hi8 _) (F.X'_ne_one hi8 harg)
  · have ho : Odd i := Int.not_even_iff_odd.mp hi
    exact T.lemma35_ii F.hT ho (F.X_mem i t) (F.X_ne_one i ht)

theorem mu_X'_mul_self {i : ℤ} (hi : Even i) {t : F.K} (ht : t ≠ 0) :
    T.mu i (F.X' i t) * T.mu i (F.X' i t) = 1 :=
  T.mu_mul_self_Uprime F.hT hi (F.X'_mem hi t) (F.X'_ne_one hi ht)

theorem mu_X_odd_conj_X {i : ℤ} (hi : Odd i) {t : F.K} (ht : t ≠ 0) (j : ℤ) (v : F.K) :
    T.mu i (F.X i t) * F.X j v * (T.mu i (F.X i t))⁻¹ =
      F.X (2 * i + 8 - j) (F.wtX t (i + 9 - j) * v) := by
  obtain ⟨k, hk⟩ := hi
  subst hk
  rw [show (2 * k + 1 : ℤ) = 1 + 2 * k by ring]
  have hkdiv : (1 + 2 * k - 1) / 2 = k := by
    rw [show 1 + 2 * k - 1 = k * 2 by ring]
    exact Int.mul_ediv_cancel k (b := 2) (by norm_num)
  have hm : T.mu (1 + 2 * k) (F.X (1 + 2 * k) t) =
      F.rho ^ k * (F.alpha t * F.a) * (F.rho ^ k)⁻¹ := by
    rw [F.mu_X_odd (i := 1 + 2 * k) ⟨k, by ring⟩ ht, hkdiv]
  have hρ : (F.rho ^ k)⁻¹ * F.X j v * F.rho ^ k = F.X (j - 2 * k) v := by
    have h := F.conj_rho_X (-k) j v
    rw [show j + 2 * (-k) = j - 2 * k by ring] at h
    simpa [zpow_neg] using h
  have hconj : (F.alpha t * F.a) * F.X (j - 2 * k) v * (F.alpha t * F.a)⁻¹ =
      F.X (10 - (j - 2 * k)) (F.wtX t (10 - (j - 2 * k)) * v) := by
    have hainv : F.a⁻¹ = F.a := inv_eq_of_mul_eq_one_right F.a_mul_self
    calc
      (F.alpha t * F.a) * F.X (j - 2 * k) v * (F.alpha t * F.a)⁻¹
          = F.alpha t * (F.a * F.X (j - 2 * k) v * F.a⁻¹) * (F.alpha t)⁻¹ := by
              rw [mul_inv_rev, hainv]
              group
      _ = F.alpha t * F.X (10 - (j - 2 * k)) v * (F.alpha t)⁻¹ := by
              rw [F.conj_a_X (j - 2 * k) v]
      _ = F.X (10 - (j - 2 * k)) (F.wtX t (10 - (j - 2 * k)) * v) :=
              F.alpha_conj_X ht (10 - (j - 2 * k)) v
  calc
    T.mu (1 + 2 * k) (F.X (1 + 2 * k) t) * F.X j v *
        (T.mu (1 + 2 * k) (F.X (1 + 2 * k) t))⁻¹
        = (F.rho ^ k * (F.alpha t * F.a) * (F.rho ^ k)⁻¹) * F.X j v *
            (F.rho ^ k * (F.alpha t * F.a) * (F.rho ^ k)⁻¹)⁻¹ := by rw [hm]
    _ = F.rho ^ k * ((F.alpha t * F.a) *
          ((F.rho ^ k)⁻¹ * F.X j v * F.rho ^ k) * (F.alpha t * F.a)⁻¹) *
            (F.rho ^ k)⁻¹ := by group
    _ = F.rho ^ k * ((F.alpha t * F.a) * F.X (j - 2 * k) v *
          (F.alpha t * F.a)⁻¹) * (F.rho ^ k)⁻¹ := by rw [hρ]
    _ = F.rho ^ k * F.X (10 - (j - 2 * k)) (F.wtX t (10 - (j - 2 * k)) * v) *
          (F.rho ^ k)⁻¹ := by rw [hconj]
    _ = F.X (10 - (j - 2 * k) + 2 * k) (F.wtX t (10 - (j - 2 * k)) * v) :=
          F.conj_rho_X k (10 - (j - 2 * k)) (F.wtX t (10 - (j - 2 * k)) * v)
    _ = F.X (2 * (1 + 2 * k) + 8 - j) (F.wtX t ((1 + 2 * k) + 9 - j) * v) := by
          rw [show 10 - (j - 2 * k) + 2 * k = 2 * (1 + 2 * k) + 8 - j by ring,
            show 10 - (j - 2 * k) = (1 + 2 * k) + 9 - j by ring]

theorem mu_X_odd_conj_X' {i : ℤ} (hi : Odd i) {t : F.K}
    (ht : t ≠ 0) {j : ℤ} (hj : Even j)
    (v : F.K) :
    T.mu i (F.X i t) * F.X' j v * (T.mu i (F.X i t))⁻¹ =
      F.X' (2 * i + 8 - j) (F.wtX' t (i + 9 - j) * v) := by
  obtain ⟨k, hk⟩ := hi
  subst hk
  rw [show (2 * k + 1 : ℤ) = 1 + 2 * k by ring]
  have hkdiv : (1 + 2 * k - 1) / 2 = k := by
    rw [show 1 + 2 * k - 1 = k * 2 by ring]
    exact Int.mul_ediv_cancel k (b := 2) (by norm_num)
  have hm : T.mu (1 + 2 * k) (F.X (1 + 2 * k) t) =
      F.rho ^ k * (F.alpha t * F.a) * (F.rho ^ k)⁻¹ := by
    rw [F.mu_X_odd (i := 1 + 2 * k) ⟨k, by ring⟩ ht, hkdiv]
  have hρ : (F.rho ^ k)⁻¹ * F.X' j v * F.rho ^ k = F.X' (j - 2 * k) v := by
    have h := F.conj_rho_X' (-k) j v
    rw [show j + 2 * (-k) = j - 2 * k by ring] at h
    simpa [zpow_neg] using h
  have hj' : Even (10 - (j - 2 * k)) := by
    obtain ⟨r, hr⟩ := hj
    exact ⟨5 - r + k, by omega⟩
  have hconj : (F.alpha t * F.a) * F.X' (j - 2 * k) v * (F.alpha t * F.a)⁻¹ =
      F.X' (10 - (j - 2 * k)) (F.wtX' t (10 - (j - 2 * k)) * v) := by
    have hainv : F.a⁻¹ = F.a := inv_eq_of_mul_eq_one_right F.a_mul_self
    have hj'' : Even (j - 2 * k) := by
      obtain ⟨r, hr⟩ := hj
      exact ⟨r - k, by omega⟩
    calc
      (F.alpha t * F.a) * F.X' (j - 2 * k) v * (F.alpha t * F.a)⁻¹
          = F.alpha t * (F.a * F.X' (j - 2 * k) v * F.a⁻¹) * (F.alpha t)⁻¹ := by
              rw [mul_inv_rev, hainv]
              group
      _ = F.alpha t * F.X' (10 - (j - 2 * k)) v * (F.alpha t)⁻¹ := by
              rw [F.conj_a_X' hj'']
      _ = F.X' (10 - (j - 2 * k)) (F.wtX' t (10 - (j - 2 * k)) * v) :=
              F.alpha_conj_X' ht (j := 10 - (j - 2 * k)) hj' v
  calc
    T.mu (1 + 2 * k) (F.X (1 + 2 * k) t) * F.X' j v *
        (T.mu (1 + 2 * k) (F.X (1 + 2 * k) t))⁻¹
        = (F.rho ^ k * (F.alpha t * F.a) * (F.rho ^ k)⁻¹) * F.X' j v *
            (F.rho ^ k * (F.alpha t * F.a) * (F.rho ^ k)⁻¹)⁻¹ := by rw [hm]
    _ = F.rho ^ k * ((F.alpha t * F.a) *
          ((F.rho ^ k)⁻¹ * F.X' j v * F.rho ^ k) * (F.alpha t * F.a)⁻¹) *
            (F.rho ^ k)⁻¹ := by group
    _ = F.rho ^ k * ((F.alpha t * F.a) * F.X' (j - 2 * k) v *
          (F.alpha t * F.a)⁻¹) * (F.rho ^ k)⁻¹ := by rw [hρ]
    _ = F.rho ^ k * F.X' (10 - (j - 2 * k)) (F.wtX' t (10 - (j - 2 * k)) * v) *
          (F.rho ^ k)⁻¹ := by rw [hconj]
    _ = F.X' (10 - (j - 2 * k) + 2 * k) (F.wtX' t (10 - (j - 2 * k)) * v) :=
          F.conj_rho_X' k (10 - (j - 2 * k)) (F.wtX' t (10 - (j - 2 * k)) * v)
    _ = F.X' (2 * (1 + 2 * k) + 8 - j) (F.wtX' t ((1 + 2 * k) + 9 - j) * v) := by
          rw [show 10 - (j - 2 * k) + 2 * k = 2 * (1 + 2 * k) + 8 - j by ring,
            show 10 - (j - 2 * k) = (1 + 2 * k) + 9 - j by ring]

theorem mu_X'_conj_X {i : ℤ} (hi : Even i) {t : F.K} (ht : t ≠ 0) (j : ℤ) (v : F.K) :
    T.mu i (F.X' i t) * F.X j v * (T.mu i (F.X' i t))⁻¹ =
      F.X (2 * i + 8 - j) (F.wtX t (i + 12 - j) / F.wtX t (j - i + 4) * v) := by
  obtain ⟨k, hk⟩ := hi
  subst hk
  have hkdiv : (k + k - 4) / 2 = k - 2 := by omega
  have hm : T.mu (k + k) (F.X' (k + k) t) =
      F.rho ^ (k - 2) * (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
        (F.rho ^ (k - 2))⁻¹ := by
    rw [F.mu_X'_even (i := k + k) ⟨k, by ring⟩ ht, hkdiv, F.mu_X'_four ht]
  have hρ : (F.rho ^ (k - 2))⁻¹ * F.X j v * F.rho ^ (k - 2) =
      F.X (j - 2 * (k - 2)) v := by
    have h := F.conj_rho_X (2 - k) j v
    rw [show j + 2 * (2 - k) = j - 2 * (k - 2) by ring] at h
    rw [show (2 - k : ℤ) = -(k - 2) by ring, zpow_neg] at h
    simpa using h
  have hαinv : (F.alpha t)⁻¹ * F.X (j - 2 * (k - 2)) v * F.alpha t =
      F.X (j - 2 * (k - 2)) (v / F.wtX t (j - 2 * (k - 2))) := by
    have h := F.alpha_conj_X ht (j - 2 * (k - 2))
      (v / F.wtX t (j - 2 * (k - 2)))
    rw [mul_div_cancel₀ v (F.wtX_ne_zero ht (j - 2 * (k - 2)))] at h
    calc
      (F.alpha t)⁻¹ * F.X (j - 2 * (k - 2)) v * F.alpha t
          = (F.alpha t)⁻¹ * (F.alpha t *
              F.X (j - 2 * (k - 2)) (v / F.wtX t (j - 2 * (k - 2))) *
                (F.alpha t)⁻¹) * F.alpha t := by rw [h]
      _ = F.X (j - 2 * (k - 2)) (v / F.wtX t (j - 2 * (k - 2))) := by group
  have hc : (F.rho ^ (-4 : ℤ) * F.b) * F.X (j - 2 * (k - 2))
        (v / F.wtX t (j - 2 * (k - 2))) * (F.rho ^ (-4 : ℤ) * F.b)⁻¹ =
      F.X (16 - (j - 2 * (k - 2))) (v / F.wtX t (j - 2 * (k - 2))) := by
    have hbinv : F.b⁻¹ = F.b := inv_eq_of_mul_eq_one_right F.b_mul_self
    calc
      (F.rho ^ (-4 : ℤ) * F.b) * F.X (j - 2 * (k - 2))
            (v / F.wtX t (j - 2 * (k - 2))) * (F.rho ^ (-4 : ℤ) * F.b)⁻¹
          = F.rho ^ (-4 : ℤ) * (F.b * F.X (j - 2 * (k - 2))
              (v / F.wtX t (j - 2 * (k - 2))) * F.b⁻¹) *
                (F.rho ^ (-4 : ℤ))⁻¹ := by
              rw [mul_inv_rev, hbinv]
              group
      _ = F.rho ^ (-4 : ℤ) * F.X (24 - (j - 2 * (k - 2)))
            (v / F.wtX t (j - 2 * (k - 2))) * (F.rho ^ (-4 : ℤ))⁻¹ := by
              rw [F.conj_b_X]
      _ = F.X (16 - (j - 2 * (k - 2))) (v / F.wtX t (j - 2 * (k - 2))) := by
              have h := F.conj_rho_X (-4) (24 - (j - 2 * (k - 2)))
                (v / F.wtX t (j - 2 * (k - 2)))
              rw [show 24 - (j - 2 * (k - 2)) + 2 * (-4) =
                16 - (j - 2 * (k - 2)) by ring] at h
              exact h
  calc
    T.mu (k + k) (F.X' (k + k) t) * F.X j v * (T.mu (k + k) (F.X' (k + k) t))⁻¹
        = (F.rho ^ (k - 2) *
              (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
                (F.rho ^ (k - 2))⁻¹) * F.X j v *
            (F.rho ^ (k - 2) *
              (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
                (F.rho ^ (k - 2))⁻¹)⁻¹ := by rw [hm]
    _ = F.rho ^ (k - 2) * (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
          ((F.rho ^ (k - 2))⁻¹ * F.X j v * F.rho ^ (k - 2)) *
            (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹)⁻¹ *
              (F.rho ^ (k - 2))⁻¹ := by group
    _ = F.rho ^ (k - 2) * (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
          F.X (j - 2 * (k - 2)) v *
            (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹)⁻¹ *
              (F.rho ^ (k - 2))⁻¹ := by rw [hρ]
    _ = F.rho ^ (k - 2) * (F.alpha t * ((F.rho ^ (-4 : ℤ) * F.b) *
          ((F.alpha t)⁻¹ * F.X (j - 2 * (k - 2)) v * F.alpha t) *
            (F.rho ^ (-4 : ℤ) * F.b)⁻¹) * (F.alpha t)⁻¹) *
              (F.rho ^ (k - 2))⁻¹ := by group
    _ = F.rho ^ (k - 2) * (F.alpha t * ((F.rho ^ (-4 : ℤ) * F.b) *
          F.X (j - 2 * (k - 2)) (v / F.wtX t (j - 2 * (k - 2))) *
            (F.rho ^ (-4 : ℤ) * F.b)⁻¹) * (F.alpha t)⁻¹) *
              (F.rho ^ (k - 2))⁻¹ := by rw [hαinv]
    _ = F.rho ^ (k - 2) * (F.alpha t *
          F.X (16 - (j - 2 * (k - 2))) (v / F.wtX t (j - 2 * (k - 2))) *
            (F.alpha t)⁻¹) * (F.rho ^ (k - 2))⁻¹ := by rw [hc]
    _ = F.rho ^ (k - 2) * F.X (16 - (j - 2 * (k - 2)))
          (F.wtX t (16 - (j - 2 * (k - 2))) *
            (v / F.wtX t (j - 2 * (k - 2)))) * (F.rho ^ (k - 2))⁻¹ := by
            rw [F.alpha_conj_X ht]
    _ = F.X (16 - (j - 2 * (k - 2)) + 2 * (k - 2))
          (F.wtX t (16 - (j - 2 * (k - 2))) *
            (v / F.wtX t (j - 2 * (k - 2)))) :=
          F.conj_rho_X (k - 2) _ _
    _ = F.X (2 * (k + k) + 8 - j)
          (F.wtX t (k + k + 12 - j) / F.wtX t (j - (k + k) + 4) * v) := by
          rw [show 16 - (j - 2 * (k - 2)) + 2 * (k - 2) = 2 * (k + k) + 8 - j by ring,
            show 16 - (j - 2 * (k - 2)) = k + k + 12 - j by ring,
            show j - 2 * (k - 2) = j - (k + k) + 4 by ring]
          congr 1
          ring

theorem mu_X'_conj_X' {i : ℤ} (hi : Even i) {t : F.K}
    (ht : t ≠ 0) {j : ℤ} (hj : Even j)
    (v : F.K) :
    T.mu i (F.X' i t) * F.X' j v * (T.mu i (F.X' i t))⁻¹ =
      F.X' (2 * i + 8 - j) (F.wtX' t (i + 12 - j) / F.wtX' t (j - i + 4) * v) := by
  obtain ⟨k, hk⟩ := hi
  subst hk
  have hkdiv : (k + k - 4) / 2 = k - 2 := by omega
  have hm : T.mu (k + k) (F.X' (k + k) t) =
      F.rho ^ (k - 2) * (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
        (F.rho ^ (k - 2))⁻¹ := by
    rw [F.mu_X'_even (i := k + k) ⟨k, by ring⟩ ht, hkdiv, F.mu_X'_four ht]
  have hρ : (F.rho ^ (k - 2))⁻¹ * F.X' j v * F.rho ^ (k - 2) =
      F.X' (j - 2 * (k - 2)) v := by
    have h := F.conj_rho_X' (2 - k) j v
    rw [show j + 2 * (2 - k) = j - 2 * (k - 2) by ring] at h
    rw [show (2 - k : ℤ) = -(k - 2) by ring, zpow_neg] at h
    simpa using h
  have hj' : Even (j - 2 * (k - 2)) := by
    obtain ⟨r, hr⟩ := hj
    exact ⟨r - (k - 2), by omega⟩
  have hj16 : Even (16 - (j - 2 * (k - 2))) := by
    obtain ⟨r, hr⟩ := hj
    exact ⟨8 - r + (k - 2), by omega⟩
  have hj24 : Even (24 - (j - 2 * (k - 2))) := by
    obtain ⟨r, hr⟩ := hj
    exact ⟨12 - r + (k - 2), by omega⟩
  have hαinv : (F.alpha t)⁻¹ * F.X' (j - 2 * (k - 2)) v * F.alpha t =
      F.X' (j - 2 * (k - 2)) (v / F.wtX' t (j - 2 * (k - 2))) := by
    have h := F.alpha_conj_X' ht (j := j - 2 * (k - 2)) hj'
      (v / F.wtX' t (j - 2 * (k - 2)))
    rw [mul_div_cancel₀ v (F.wtX'_ne_zero ht (j - 2 * (k - 2)))] at h
    calc
      (F.alpha t)⁻¹ * F.X' (j - 2 * (k - 2)) v * F.alpha t
          = (F.alpha t)⁻¹ * (F.alpha t *
              F.X' (j - 2 * (k - 2)) (v / F.wtX' t (j - 2 * (k - 2))) *
                (F.alpha t)⁻¹) * F.alpha t := by rw [h]
      _ = F.X' (j - 2 * (k - 2)) (v / F.wtX' t (j - 2 * (k - 2))) := by group
  have hc : (F.rho ^ (-4 : ℤ) * F.b) * F.X' (j - 2 * (k - 2))
        (v / F.wtX' t (j - 2 * (k - 2))) * (F.rho ^ (-4 : ℤ) * F.b)⁻¹ =
      F.X' (16 - (j - 2 * (k - 2))) (v / F.wtX' t (j - 2 * (k - 2))) := by
    have hbinv : F.b⁻¹ = F.b := inv_eq_of_mul_eq_one_right F.b_mul_self
    calc
      (F.rho ^ (-4 : ℤ) * F.b) * F.X' (j - 2 * (k - 2))
            (v / F.wtX' t (j - 2 * (k - 2))) * (F.rho ^ (-4 : ℤ) * F.b)⁻¹
          = F.rho ^ (-4 : ℤ) * (F.b * F.X' (j - 2 * (k - 2))
              (v / F.wtX' t (j - 2 * (k - 2))) * F.b⁻¹) *
                (F.rho ^ (-4 : ℤ))⁻¹ := by
              rw [mul_inv_rev, hbinv]
              group
      _ = F.rho ^ (-4 : ℤ) * F.X' (24 - (j - 2 * (k - 2)))
            (v / F.wtX' t (j - 2 * (k - 2))) * (F.rho ^ (-4 : ℤ))⁻¹ := by
              rw [F.conj_b_X' (j := j - 2 * (k - 2)) hj']
      _ = F.X' (16 - (j - 2 * (k - 2))) (v / F.wtX' t (j - 2 * (k - 2))) := by
              have h := F.conj_rho_X' (-4) (24 - (j - 2 * (k - 2)))
                (v / F.wtX' t (j - 2 * (k - 2)))
              rw [show 24 - (j - 2 * (k - 2)) + 2 * (-4) =
                16 - (j - 2 * (k - 2)) by ring] at h
              exact h
  calc
    T.mu (k + k) (F.X' (k + k) t) * F.X' j v * (T.mu (k + k) (F.X' (k + k) t))⁻¹
        = (F.rho ^ (k - 2) *
              (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
                (F.rho ^ (k - 2))⁻¹) * F.X' j v *
            (F.rho ^ (k - 2) *
              (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
                (F.rho ^ (k - 2))⁻¹)⁻¹ := by rw [hm]
    _ = F.rho ^ (k - 2) * (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
          ((F.rho ^ (k - 2))⁻¹ * F.X' j v * F.rho ^ (k - 2)) *
            (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹)⁻¹ *
              (F.rho ^ (k - 2))⁻¹ := by group
    _ = F.rho ^ (k - 2) * (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹) *
          F.X' (j - 2 * (k - 2)) v *
            (F.alpha t * (F.rho ^ (-4 : ℤ) * F.b) * (F.alpha t)⁻¹)⁻¹ *
              (F.rho ^ (k - 2))⁻¹ := by rw [hρ]
    _ = F.rho ^ (k - 2) * (F.alpha t * ((F.rho ^ (-4 : ℤ) * F.b) *
          ((F.alpha t)⁻¹ * F.X' (j - 2 * (k - 2)) v * F.alpha t) *
            (F.rho ^ (-4 : ℤ) * F.b)⁻¹) * (F.alpha t)⁻¹) *
              (F.rho ^ (k - 2))⁻¹ := by group
    _ = F.rho ^ (k - 2) * (F.alpha t * ((F.rho ^ (-4 : ℤ) * F.b) *
          F.X' (j - 2 * (k - 2)) (v / F.wtX' t (j - 2 * (k - 2))) *
            (F.rho ^ (-4 : ℤ) * F.b)⁻¹) * (F.alpha t)⁻¹) *
              (F.rho ^ (k - 2))⁻¹ := by rw [hαinv]
    _ = F.rho ^ (k - 2) * (F.alpha t *
          F.X' (16 - (j - 2 * (k - 2))) (v / F.wtX' t (j - 2 * (k - 2))) *
            (F.alpha t)⁻¹) * (F.rho ^ (k - 2))⁻¹ := by rw [hc]
    _ = F.rho ^ (k - 2) * F.X' (16 - (j - 2 * (k - 2)))
          (F.wtX' t (16 - (j - 2 * (k - 2))) *
            (v / F.wtX' t (j - 2 * (k - 2)))) * (F.rho ^ (k - 2))⁻¹ := by
            rw [F.alpha_conj_X' ht (j := 16 - (j - 2 * (k - 2))) hj16]
    _ = F.X' (16 - (j - 2 * (k - 2)) + 2 * (k - 2))
          (F.wtX' t (16 - (j - 2 * (k - 2))) *
            (v / F.wtX' t (j - 2 * (k - 2)))) :=
          F.conj_rho_X' (k - 2) _ _
    _ = F.X' (2 * (k + k) + 8 - j)
          (F.wtX' t (k + k + 12 - j) / F.wtX' t (j - (k + k) + 4) * v) := by
          rw [show 16 - (j - 2 * (k - 2)) + 2 * (k - 2) = 2 * (k + k) + 8 - j by ring,
            show 16 - (j - 2 * (k - 2)) = k + k + 12 - j by ring,
            show j - 2 * (k - 2) = j - (k + k) + 4 by ring]
          congr 1
          ring

theorem nu_X_odd {j : ℤ} (hj : Odd j) {t : F.K} (ht : t ≠ 0) :
    T.nu j (F.X j t) = F.X (j + 8) t⁻¹ := by
  have hu : F.X j t ∈ T.U j := F.X_mem j t
  have hu1 : F.X j t ≠ 1 := F.X_ne_one j ht
  rw [(T.nu_odd F.hT hj hu hu1).1]
  have h := F.mu_X_odd_conj_X hj ht j t
  rw [show 2 * j + 8 - j = j + 8 by ring,
    show j + 9 - j = 9 by ring,
    show F.wtX t 9 = (t ^ 2)⁻¹ by
      simp only [OctFrame.wtX]
      norm_num] at h
  rw [h]
  congr 1
  field_simp [ht]

theorem nu'_X_odd {j : ℤ} (hj : Odd j) {t : F.K} (ht : t ≠ 0) :
    T.nu' j (F.X j t) = F.X (j + 8) t⁻¹ := by
  have hu : F.X j t ∈ T.U j := F.X_mem j t
  have hu1 : F.X j t ≠ 1 := F.X_ne_one j ht
  have h := T.nu_inv (by norm_num : 3 ≤ 8) hu hu1
  rw [F.X_inv_odd hj t, F.nu_X_odd hj ht] at h
  have hodd : Odd (j + 8) := hj.add_even (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
  have hXinv : (F.X (j + 8) (t⁻¹))⁻¹ = F.X (j + 8) (t⁻¹) := F.X_inv_odd hodd _
  have h' := congrArg Inv.inv h
  rw [hXinv] at h'
  simpa using h'.symm

theorem nu'_X' {j : ℤ} (hj : Even j) {t : F.K} (ht : t ≠ 0) :
    T.nu' j (F.X' j t) = F.X (j + 8) (t / F.sigma t) := by
  have hσt : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  set s : F.K := t / F.sigma t with hs
  have hs0 : s ≠ 0 := div_ne_zero ht hσt
  have harg : (F.sigma s * s)⁻¹ = t := by
    rw [hs]
    have hσs : F.sigma (t / F.sigma t) = F.sigma t / t ^ 2 := by
      rw [map_div₀, F.sigma_sigma]
    rw [hσs]
    field_simp [ht, hσt]
  have h1 : F.X (j - 8) s = T.nu' j (F.X' j t) := by
    have hxs := F.xs_of_ne_zero (j := j - 8) (x := s) hs0
    rw [F.X_of_even (j := j - 8) (by
      exact hj.sub (show Even (8 : ℤ) from ⟨4, by norm_num⟩)) s, hxs, F.X'_def]
    rw [show (j - 8) + 8 = j by ring, harg]
  have h2 : F.X (j + 8) s = F.X (j - 8) s := by
    have h := F.X_add_sixteen (j - 8) s
    rw [show (j - 8) + 16 = j + 8 by ring] at h
    exact h
  rw [← h1]
  exact h2.symm

theorem nu_X' {j : ℤ} (hj : Even j) {t : F.K} (ht : t ≠ 0) :
    T.nu j (F.X' j t) = (F.X (j + 8) (t / F.sigma t))⁻¹ := by
  have hu : F.X' j t ∈ T.Uprime j := F.X'_mem hj t
  have hu1 : F.X' j t ≠ 1 := F.X'_ne_one hj ht
  rw [T.lemma316_i F.hT hj hu hu1, F.nu'_X' hj ht]

theorem nu_X_even {j : ℤ} (hj : Even j) {t : F.K} (ht : t ≠ 0) :
    T.nu j (F.X j t) = F.X' (j + 8) (F.sigma t * t)⁻¹ := by
  have hσt : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  have harg : (F.sigma t * t)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hσt ht)
  have hj8 : Even (j + 8) := hj.add (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
  have hXs : F.X j t = T.nu' (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) := by
    rw [F.X_of_even hj, F.xs_of_ne_zero ht, F.X'_def]
  rw [hXs]
  have h := (T.mu_nu' (by norm_num : 3 ≤ 8) (i := j + 8)
    (u := F.X' (j + 8) (F.sigma t * t)⁻¹)
    (T.Uprime_le (j + 8) (F.X'_mem hj8 _))
    (F.X'_ne_one hj8 harg)).2
  rw [show j + 8 + ((8 : ℕ) : ℤ) = j + 16 by ring] at h
  calc
    T.nu j (T.nu' (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹)) =
        T.nu (j + 16) (T.nu' (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹)) := by
      rw [show j + 16 = j + 2 * ((8 : ℕ) : ℤ) * 1 by ring]
      rw [T.nu_add_two_mul (by norm_num : 3 ≤ 8)]
    _ = F.X' (j + 8) (F.sigma t * t)⁻¹ := h

theorem nu'_X_even {j : ℤ} (hj : Even j) {t : F.K} (ht : t ≠ 0) :
    T.nu' j (F.X j t) = (F.X (j + 8) t⁻¹)⁻¹ := by
  have hst : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  have hj8 : Even (j + 8) := hj.add (by decide)
  have hs0 : (F.sigma t * t)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hst ht)
  have hσs : F.sigma (F.sigma t * t)⁻¹ = (t ^ 2 * F.sigma t)⁻¹ := by
    rw [map_inv₀, map_mul, F.sigma_sigma]
  have hsσ : (F.sigma t * t)⁻¹ / F.sigma (F.sigma t * t)⁻¹ = t := by
    rw [hσs]
    field_simp
  have huP : F.X' (j + 8) (F.sigma t * t)⁻¹ ∈ T.Uprime (j + 8) := F.X'_mem hj8 _
  have huU : F.X' (j + 8) (F.sigma t * t)⁻¹ ∈ T.U (j + 8) := T.Uprime_le _ huP
  have hu1 : F.X' (j + 8) (F.sigma t * t)⁻¹ ≠ 1 := F.X'_ne_one hj8 hs0
  have hvU : (F.X j t)⁻¹ ∈ T.U j := (T.U j).inv_mem (F.X_mem j t)
  have hv1 : (F.X j t)⁻¹ ≠ 1 := inv_ne_one.mpr (F.X_ne_one j ht)
  have hnu : T.nu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) = (F.X j t)⁻¹ := by
    rw [F.nu_X' hj8 hs0, hsσ, show j + 8 + 8 = j + 16 by ring, F.X_add_sixteen]
  have hnu' : T.nu' (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) = (F.X j t)⁻¹⁻¹ := by
    have h316 := T.lemma316_i F.hT hj8 huP hu1
    rw [hnu] at h316
    rw [h316, inv_inv]
  have hm : T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) =
      (F.X j t)⁻¹ * F.X' (j + 8) (F.sigma t * t)⁻¹ * (F.X j t)⁻¹⁻¹ := by
    rw [TitsSystem.mu, hnu, hnu']
  have hmoves := T.moves_mu huU hu1
  have hper : ∀ k : ℤ, T.U (2 * (j + 8) + ((8 : ℕ) : ℤ) - k) =
      T.U (2 * j + ((8 : ℕ) : ℤ) - k) := by
    intro k
    rw [show 2 * (j + 8) + ((8 : ℕ) : ℤ) - k =
      (2 * j + ((8 : ℕ) : ℤ) - k) + 2 * ((8 : ℕ) : ℤ) * 1 by
      push_cast
      ring]
    exact U_add_two_mul T _ 1
  have hmv : T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) * (F.X j t)⁻¹ *
      (T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹))⁻¹ ∈
        T.U (j + ((8 : ℕ) : ℤ)) := by
    have h1 := TitsSystem.Moves.conj_mem T hmoves hvU
    change _ ∈ T.U (2 * (j + 8) + ((8 : ℕ) : ℤ) - j) at h1
    rw [show 2 * (j + 8) + ((8 : ℕ) : ℤ) - j =
      (j + ((8 : ℕ) : ℤ)) + 2 * ((8 : ℕ) : ℤ) * 1 by
      push_cast
      ring, U_add_two_mul] at h1
    exact h1
  have hisMu : T.IsMu j (F.X j t)⁻¹
      (T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) * (F.X j t)⁻¹ *
        (T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹))⁻¹)⁻¹
      (F.X' (j + 8) (F.sigma t * t)⁻¹) := by
    refine ⟨(T.U _).inv_mem hmv, by exact_mod_cast huU, fun k => ?_⟩
    have e : (T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) * (F.X j t)⁻¹ *
        (T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹))⁻¹)⁻¹ * (F.X j t)⁻¹ *
        F.X' (j + 8) (F.sigma t * t)⁻¹ =
          T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) := by
      rw [hm]
      group
    rw [e, hmoves k]
    exact_mod_cast hper k
  have hpair := T.isMu_unique (by norm_num : 3 ≤ 8) hvU hv1 (T.isMu_nu hvU hv1) hisMu
  have hconj : T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹) * F.X j t *
      (T.mu (j + 8) (F.X' (j + 8) (F.sigma t * t)⁻¹))⁻¹ = F.X (j + 8) t⁻¹ := by
    rw [F.mu_X'_conj_X hj8 hs0 j t,
      show 2 * (j + 8) + 8 - j = (j + 8) + 16 by ring,
      F.X_add_sixteen, show j + 8 + 12 - j = 20 by ring,
      show j - (j + 8) + 4 = -4 by ring]
    congr 1
    norm_num [OctFrame.wtX]
    rw [F.sigma_sigma t]
    field_simp [ht, hst]
  have hinv := T.nu_inv (by norm_num : 3 ≤ 8) (F.X_mem j t) (F.X_ne_one j ht)
  have key := inv_injective (hinv.symm.trans hpair.1)
  rw [key, ← hconj]
  group

theorem c12 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (1 + s) t * F.X (2 + s) u = F.X (2 + s) u * F.X (1 + s) t := by
  have hy : F.X (2 + s) u ∈ T.U ((1 + s) + 1) := by
    rw [show (1 + s) + 1 = 2 + s by ring]
    exact F.X_mem (2 + s) u
  exact T.comm_add_one (F.X_mem (1 + s) t) hy

theorem c12' (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (1 + s) t * F.X' (2 + s) u = F.X' (2 + s) u * F.X (1 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  have hy : F.X' (2 + s) u ∈ T.U ((1 + s) + 1) := by
    rw [show (1 + s) + 1 = 2 + s by ring]
    exact T.Uprime_le (2 + s) (F.X'_mem h2 u)
  exact T.comm_add_one (F.X_mem (1 + s) t) hy

theorem c13 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (1 + s) t * F.X (3 + s) u = F.X (3 + s) u * F.X (1 + s) t := by
  have ho : Odd (1 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k, by omega⟩
  have hy : F.X (3 + s) u ∈ T.U ((1 + s) + 2) := by
    rw [show (1 + s) + 2 = 3 + s by ring]
    exact F.X_mem (3 + s) u
  exact T.comm_odd_add_two F.hT ho (F.X_mem (1 + s) t) hy

theorem c14' (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (1 + s) t * F.X' (4 + s) u = F.X' (4 + s) u * F.X (1 + s) t := by
  have h4 : Even (4 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 2, by omega⟩
  exact (T.Uprime_comm (j := 4 + s) (k := 1 + s) (by omega) (by omega)
    (F.X'_mem h4 u) (F.X_mem (1 + s) t)).symm

theorem c15 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (1 + s) t * F.X (5 + s) u = F.X (5 + s) u * F.X (1 + s) t := by
  have ho : Odd (1 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k, by omega⟩
  have hy : F.X (5 + s) u ∈ T.U ((1 + s) + 4) := by
    rw [show (1 + s) + 4 = 5 + s by ring]
    exact F.X_mem (5 + s) u
  exact T.comm_odd_add_four F.hT ho (F.X_mem (1 + s) t) hy

theorem c23 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (2 + s) t * F.X (3 + s) u = F.X (3 + s) u * F.X (2 + s) t := by
  have hy : F.X (3 + s) u ∈ T.U ((2 + s) + 1) := by
    rw [show (2 + s) + 1 = 3 + s by ring]
    exact F.X_mem (3 + s) u
  exact T.comm_add_one (F.X_mem (2 + s) t) hy

theorem c2'3 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X' (2 + s) t * F.X (3 + s) u = F.X (3 + s) u * F.X' (2 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  exact T.Uprime_comm (j := 2 + s) (k := 3 + s) (by omega) (by omega)
    (F.X'_mem h2 t) (F.X_mem (3 + s) u)

theorem c2'4 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X' (2 + s) t * F.X (4 + s) u = F.X (4 + s) u * F.X' (2 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  exact T.Uprime_comm (j := 2 + s) (k := 4 + s) (by omega) (by omega)
    (F.X'_mem h2 t) (F.X_mem (4 + s) u)

theorem c2'4' (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X' (2 + s) t * F.X' (4 + s) u = F.X' (4 + s) u * F.X' (2 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  have h4 : Even (4 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 2, by omega⟩
  exact T.Uprime_comm (j := 2 + s) (k := 4 + s) (by omega) (by omega)
    (F.X'_mem h2 t) (T.Uprime_le (4 + s) (F.X'_mem h4 u))

theorem c24' (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (2 + s) t * F.X' (4 + s) u = F.X' (4 + s) u * F.X (2 + s) t := by
  have h4 : Even (4 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 2, by omega⟩
  exact (T.Uprime_comm (j := 4 + s) (k := 2 + s) (by omega) (by omega)
    (F.X'_mem h4 u) (F.X_mem (2 + s) t)).symm

theorem c2'5 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X' (2 + s) t * F.X (5 + s) u = F.X (5 + s) u * F.X' (2 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  exact T.Uprime_comm (j := 2 + s) (k := 5 + s) (by omega) (by omega)
    (F.X'_mem h2 t) (F.X_mem (5 + s) u)

theorem c26 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (2 + s) t * F.X (6 + s) u = F.X (6 + s) u * F.X (2 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  have hy : F.X (6 + s) u ∈ T.U ((2 + s) + 4) := by
    rw [show (2 + s) + 4 = 6 + s by ring]
    exact F.X_mem (6 + s) u
  exact T.comm_even_add_four F.hT h2 (F.X_mem (2 + s) t) hy

theorem c26' (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X (2 + s) t * F.X' (6 + s) u = F.X' (6 + s) u * F.X (2 + s) t := by
  have h6 : Even (6 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 3, by omega⟩
  exact (T.Uprime_comm (j := 6 + s) (k := 2 + s) (by omega) (by omega)
    (F.X'_mem h6 u) (F.X_mem (2 + s) t)).symm

theorem c2'6 (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X' (2 + s) t * F.X (6 + s) u = F.X (6 + s) u * F.X' (2 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  exact T.Uprime_comm (j := 2 + s) (k := 6 + s) (by omega) (by omega)
    (F.X'_mem h2 t) (F.X_mem (6 + s) u)

theorem c2'6' (s : ℤ) (hs : Even s) (t u : F.K) :
    F.X' (2 + s) t * F.X' (6 + s) u = F.X' (6 + s) u * F.X' (2 + s) t := by
  have h2 : Even (2 + s) := even_two.add hs
  have h6 : Even (6 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 3, by omega⟩
  exact T.Uprime_comm (j := 2 + s) (k := 6 + s) (by omega) (by omega)
    (F.X'_mem h2 t) (T.Uprime_le (6 + s) (F.X'_mem h6 u))

theorem r3 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (1 + s) t, F.X' (6 + s) u⁆ = F.X' (4 + s) (t * u) := by
  have h4 : Even (4 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 2, by omega⟩
  have ho : Odd (1 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k, by omega⟩
  have h := F.comm_xo_xp h4 t u
  rw [show (4 + s) - 3 = 1 + s by ring, show (4 + s) + 2 = 6 + s by ring] at h
  simpa [F.X_of_odd ho, F.X'_def] using h

theorem r10 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X' (2 + s) t, F.X (7 + s) u⁆ = F.X' (4 + s) (t * u) := by
  have h4 : Even (4 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 2, by omega⟩
  have ho : Odd (7 + s) := by
    obtain ⟨k, hk⟩ := hs
    exact ⟨k + 3, by omega⟩
  have h := F.comm_xo_xp' h4 u t
  rw [show (4 + s) + 3 = 7 + s by ring, show (4 + s) - 2 = 2 + s by ring] at h
  rw [← commutatorElement_inv (F.X (7 + s) u) (F.X' (2 + s) t)]
  rw [show F.X (7 + s) u = F.xo (7 + s) u.val from F.X_of_odd ho u,
    F.X'_def (2 + s) t]
  rw [h]
  rw [show F.xp (4 + s) (u * t).val = F.X' (4 + s) (u * t) from rfl,
    F.X'_inv h4, mul_comm]

theorem r5 (s : ℤ) (hs : Even s) (t u : F.K) :
    ⁅F.X (1 + s) t, F.X (7 + s) u⁆ =
      F.X (3 + s) (F.sigma t * u) * F.X (5 + s) (t * F.sigma u) := by
  have h0 : ⁅F.X 1 t, F.X 7 u⁆ = F.X 3 (F.sigma t * u) * F.X 5 (t * F.sigma u) := by
    have h := F.comm_xo_one_xo_seven t u
    rw [F.X_of_odd (by decide : Odd (1 : ℤ)) t,
      F.X_of_odd (by decide : Odd (7 : ℤ)) u,
      F.X_of_odd (by decide : Odd (3 : ℤ)) (F.sigma t * u),
      F.X_of_odd (by decide : Odd (5 : ℤ)) (t * F.sigma u)]
    simpa [F.sigma_apply] using h
  obtain ⟨k, hk⟩ := hs
  have h := congrArg (MulAut.conj (F.rho ^ k)) h0
  simp only [map_commutatorElement, map_mul, MulAut.conj_apply, F.conj_rho_X] at h
  rwa [show (1 : ℤ) + 2 * k = 1 + s by omega,
    show (7 : ℤ) + 2 * k = 7 + s by omega,
    show (3 : ℤ) + 2 * k = 3 + s by omega,
    show (5 : ℤ) + 2 * k = 5 + s by omega] at h

end OctFrame

end CFSG.GH74.Tits83
