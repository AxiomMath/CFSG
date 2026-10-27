module

public import CFSG.CGT.Stroth77.Stroth34T200Coord

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T200

variable {m : ℕ}

theorem t200_exists_vec (x : Torus (StrothTypeIndex.t200 m).k) :
    ∃ a b c : ℤ, x = Torus.ofInt (StrothTypeIndex.t200 m).k ![a, b, c] := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  refine ⟨v 0, v 1, v 2, ?_⟩
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_vec_eq_iff (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![a, b, c] = Torus.ofInt _ ![a', b', c'] ↔
      (2 : ℤ) ^ m ∣ a' - a ∧ (2 : ℤ) ^ (m + 2) ∣ b' - b ∧ (2 : ℤ) ^ (m + 2) ∣ c' - c :=
  t200_ofInt_eq_iff ![a, b, c] ![a', b', c']

theorem t200_vec_eq_zero_iff (a b c : ℤ) :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![a, b, c] = 0 ↔
      (2 : ℤ) ^ m ∣ a ∧ (2 : ℤ) ^ (m + 2) ∣ b ∧ (2 : ℤ) ^ (m + 2) ∣ c :=
  t200_ofInt_eq_zero_iff ![a, b, c]

theorem t200_add_vec (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![a, b, c] + Torus.ofInt _ ![a', b', c'] =
      Torus.ofInt _ ![a + a', b + b', c + c'] := by
  rw [← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_sub_vec (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t200 m).k ![a, b, c] - Torus.ofInt _ ![a', b', c'] =
      Torus.ofInt _ ![a - a', b - b', c - c'] := by
  rw [← Torus.ofInt_sub]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_neg_vec (a b c : ℤ) :
    -Torus.ofInt (StrothTypeIndex.t200 m).k ![a, b, c] = Torus.ofInt _ ![-a, -b, -c] := by
  rw [← Torus.ofInt_neg]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_zsmul_vec (z a b c : ℤ) :
    z • Torus.ofInt (StrothTypeIndex.t200 m).k ![a, b, c] =
      Torus.ofInt _ ![z * a, z * b, z * c] := by
  rw [← Torus.ofInt_zsmul]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t200_φuv_vec (a b c : ℤ) :
    (StrothTypeIndex.t200 m).action.φuv (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![-3 * a + b + c, -4 * a + b + 2 * c, -4 * a + 2 * b + c] :=
  t200_φuv ![a, b, c]

theorem t200_φt_vec (a b c : ℤ) :
    (StrothTypeIndex.t200 m).action.φt (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a - c, 4 * a - b - 2 * c, -c] :=
  t200_φt ![a, b, c]

theorem t200_φu_vec (a b c : ℤ) :
    (StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a, c, b] :=
  t200_φu ![a, b, c]

theorem t200_φρ_vec (a b c : ℤ) :
    (StrothTypeIndex.t200 m).action.φρ (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a - c, -c, b - c] :=
  t200_φρ ![a, b, c]

theorem not_two_pow_succ_dvd_mul_odd (j : ℕ) {z : ℤ} (hz : z % 2 = 1) :
    ¬ (2 : ℤ) ^ (j + 1) ∣ 2 ^ j * z := by
  rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)]
  omega

theorem t200_scalar (θ : Torus (StrothTypeIndex.t200 m).k →+ Torus (StrothTypeIndex.t200 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t200 m).action.φuv x) =
      (StrothTypeIndex.t200 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t200 m).action.φt x) = (StrothTypeIndex.t200 m).action.φt (θ x))
    (hu : ∀ x, θ ((StrothTypeIndex.t200 m).action.φu x) = (StrothTypeIndex.t200 m).action.φu (θ x))
    (hρ : ∀ x, θ ((StrothTypeIndex.t200 m).action.φρ x) =
      (StrothTypeIndex.t200 m).action.φρ (θ x)) :
    ∃ y : ℤ, ∀ x, θ x = y • x := by
  have F1 : (StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ ![0, 1, 0]) =
      Torus.ofInt _ ![0, 0, 1] := t200_φu_vec 0 1 0
  have F2 : (StrothTypeIndex.t200 m).action.φρ (Torus.ofInt _ ![0, 1, 0]) =
      Torus.ofInt _ ![0, 0, 1] := by
    rw [t200_φρ_vec, t200_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  have F3 : (StrothTypeIndex.t200 m).action.φt (Torus.ofInt _ ![0, 1, 0]) =
      -Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0] := by
    rw [t200_φt_vec, t200_neg_vec, t200_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  obtain ⟨v0, v1, v2, hv⟩ :=
    t200_exists_vec (θ (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0]))
  have e1 : (StrothTypeIndex.t200 m).action.φu (θ (Torus.ofInt _ ![0, 1, 0])) =
      (StrothTypeIndex.t200 m).action.φρ (θ (Torus.ofInt _ ![0, 1, 0])) := by
    rw [← hu, ← hρ, F1, F2]
  rw [hv, t200_φu_vec, t200_φρ_vec, t200_vec_eq_iff] at e1
  obtain ⟨-, -, ⟨ku, hku⟩⟩ := e1
  have e2 : (StrothTypeIndex.t200 m).action.φt (θ (Torus.ofInt _ ![0, 1, 0])) =
      -θ (Torus.ofInt _ ![0, 1, 0]) := by
    rw [← ht, F3, map_neg]
  rw [hv, t200_φt_vec, t200_neg_vec, t200_vec_eq_iff] at e2
  obtain ⟨-, ⟨kt, hkt⟩, -⟩ := e2
  have hv0 : v0 = 2 ^ m * (-(kt + 2 * ku)) :=
    mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) (by linear_combination -hkt - 2 * hku)
  have hθa : θ (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0]) =
      v1 • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 1, 0] := by
    rw [hv, t200_zsmul_vec, t200_vec_eq_iff]
    exact ⟨⟨kt + 2 * ku, by linear_combination -hv0⟩, ⟨0, by ring⟩,
      ⟨ku, by linear_combination hku⟩⟩
  have hθb : θ (Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, 1]) =
      v1 • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, 0, 1] := by
    rw [← F2, hρ, hθa, map_zsmul]
  have hc : Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] =
      (StrothTypeIndex.t200 m).action.φuv (Torus.ofInt _ ![0, 1, 0]) -
        Torus.ofInt _ ![0, 1, 0] -
        (2 : ℤ) • (StrothTypeIndex.t200 m).action.φρ (Torus.ofInt _ ![0, 1, 0]) := by
    rw [F2, t200_φuv_vec, t200_zsmul_vec, t200_sub_vec, t200_sub_vec, t200_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  have hθc : θ (Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0]) =
      v1 • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] := by
    rw [hc, map_sub, map_sub, map_zsmul, huv, hρ, hθa, map_zsmul, map_zsmul]
    module
  refine ⟨v1, fun x => ?_⟩
  obtain ⟨w0, w1, w2, rfl⟩ := t200_exists_vec x
  have hx : Torus.ofInt (StrothTypeIndex.t200 m).k ![w0, w1, w2] =
      w0 • Torus.ofInt _ ![1, 0, 0] + w1 • Torus.ofInt _ ![0, 1, 0] +
        w2 • Torus.ofInt _ ![0, 0, 1] := by
    rw [t200_zsmul_vec, t200_zsmul_vec, t200_zsmul_vec, t200_add_vec, t200_add_vec,
      t200_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  rw [hx, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hθa, hθb, hθc]
  module

theorem t200_fix_ρ (x : Torus (StrothTypeIndex.t200 m).k)
    (h : (StrothTypeIndex.t200 m).action.φρ x = x) :
    ∃ l : ℤ, x = l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] := by
  obtain ⟨a, b, c, rfl⟩ := t200_exists_vec x
  rw [t200_φρ_vec, t200_vec_eq_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  have hc : IsCoprime ((2 : ℤ) ^ (m + 2)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  obtain ⟨k3, hk3⟩ : (2 : ℤ) ^ (m + 2) ∣ c :=
    hc.dvd_of_dvd_mul_right ⟨k1 + k2, by linear_combination hk1 + hk2⟩
  refine ⟨a, ?_⟩
  rw [t200_zsmul_vec, t200_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨k3 - k1, by linear_combination -hk1 + hk3⟩,
    ⟨-k3, by linear_combination -hk3⟩⟩

theorem t200_normal_form (ruv rt : Torus (StrothTypeIndex.t200 m).k)
    (hu : (StrothTypeIndex.t200 m).action.φu ruv = ruv)
    (hρ1 : (StrothTypeIndex.t200 m).action.φρ (ruv + (StrothTypeIndex.t200 m).action.φuv rt) = ruv)
    (hρ2 : (StrothTypeIndex.t200 m).action.φρ ruv = rt) :
    ∃ p : ℤ, ruv = p • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 1, 1] ∧
      rt = p • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0] := by
  obtain ⟨a, b, c, rfl⟩ := t200_exists_vec ruv
  subst hρ2
  rw [t200_φu_vec, t200_vec_eq_iff] at hu
  rw [t200_φρ_vec, t200_φuv_vec, t200_add_vec, t200_φρ_vec, t200_vec_eq_iff] at hρ1
  obtain ⟨-, ⟨k1, hk1⟩, -⟩ := hu
  obtain ⟨⟨k2, hk2⟩, -, -⟩ := hρ1
  refine ⟨b, ?_, ?_⟩
  · rw [t200_zsmul_vec, t200_vec_eq_iff]
    exact ⟨⟨k2 + 4 * k1, by linear_combination hk2 + hk1⟩, ⟨0, by ring⟩,
      ⟨k1, by linear_combination hk1⟩⟩
  · rw [t200_φρ_vec, t200_zsmul_vec, t200_vec_eq_iff]
    exact ⟨⟨k2, by linear_combination hk2⟩, ⟨-k1, by linear_combination -hk1⟩,
      ⟨-k1, by linear_combination -hk1⟩⟩

theorem t200_noInv_uv (hm : 1 ≤ m) {q : ℤ} (hq : (4 : ℤ) ∣ q - 2) (l : ℤ)
    (d : Torus (StrothTypeIndex.t200 m).k) :
    (1 + 2 ^ (m + 1) : ℤ) • d + (StrothTypeIndex.t200 m).action.φuv d +
      l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] +
      q • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 1, 1] ≠ 0 := by
  intro h
  obtain ⟨a, b, c, rfl⟩ := t200_exists_vec d
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [t200_φuv_vec, t200_zsmul_vec, t200_zsmul_vec, t200_zsmul_vec, t200_add_vec, t200_add_vec,
    t200_add_vec, t200_vec_eq_zero_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  have hP : (2 : ℤ) ^ m' ≠ 0 := by positivity
  have hdiff : (2 : ℤ) ^ m' * (4 * (b - c - 2 * (k1 - k2))) = 0 := by
    linear_combination hk1 - hk2
  have hbc : b - c = 2 * (k1 - k2) := by
    rcases mul_eq_zero.mp hdiff with h0 | h0
    · exact absurd h0 hP
    · omega
  have h4 : (4 : ℤ) ∣ q :=
    ⟨2 * 2 ^ m' * k1 + a - 2 ^ m' * b - c - (k1 - k2), by linear_combination hk1 - 2 * hbc⟩
  omega

theorem t200_noInv_t (hm : 1 ≤ m) {q : ℤ} (hq : (4 : ℤ) ∣ q - 2) (l : ℤ)
    (d : Torus (StrothTypeIndex.t200 m).k) :
    (1 + 2 ^ (m + 1) : ℤ) • d + (StrothTypeIndex.t200 m).action.φt d +
      l • Torus.ofInt (StrothTypeIndex.t200 m).k ![1, 0, 0] +
      q • Torus.ofInt (StrothTypeIndex.t200 m).k ![0, -1, 0] ≠ 0 := by
  intro h
  obtain ⟨a, b, c, rfl⟩ := t200_exists_vec d
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [t200_φt_vec, t200_zsmul_vec, t200_zsmul_vec, t200_zsmul_vec, t200_add_vec, t200_add_vec,
    t200_add_vec, t200_vec_eq_zero_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  have hP : (2 : ℤ) ^ m' ≠ 0 := by positivity
  have hdiff : (2 : ℤ) ^ m' * (4 * (c - 2 * k2)) = 0 := by linear_combination hk2
  have hc : c = 2 * k2 := by
    rcases mul_eq_zero.mp hdiff with h0 | h0
    · exact absurd h0 hP
    · omega
  have h4 : (4 : ℤ) ∣ q :=
    ⟨2 ^ m' * b + a - k2 - 2 * 2 ^ m' * k1, by linear_combination -hk1 - 2 * hc⟩
  omega

theorem t200_fix_uv_exp (d : Torus (StrothTypeIndex.t200 m).k)
    (h : (StrothTypeIndex.t200 m).action.φuv d = d) : (2 ^ (m + 1) : ℤ) • d = 0 := by
  obtain ⟨a, b, c, rfl⟩ := t200_exists_vec d
  rw [t200_φuv_vec, t200_vec_eq_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  rw [t200_zsmul_vec, t200_vec_eq_zero_iff]
  exact ⟨⟨2 * a, by ring⟩, ⟨a - 2 ^ m * k2, by linear_combination (-(2 : ℤ) ^ m) * hk2⟩,
    ⟨a - 2 ^ m * k1, by linear_combination (-(2 : ℤ) ^ m) * hk1⟩⟩

theorem t200_fix_t_exp (d : Torus (StrothTypeIndex.t200 m).k)
    (h : (StrothTypeIndex.t200 m).action.φt d = d) : (2 ^ (m + 1) : ℤ) • d = 0 := by
  obtain ⟨a, b, c, rfl⟩ := t200_exists_vec d
  rw [t200_φt_vec, t200_vec_eq_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  rw [t200_zsmul_vec, t200_vec_eq_zero_iff]
  exact ⟨⟨2 * a, by ring⟩,
    ⟨a - 2 ^ m * k2 + 2 ^ m * k1, by linear_combination (2 : ℤ) ^ m * hk1 - (2 : ℤ) ^ m * hk2⟩,
    ⟨2 ^ m * k2, by linear_combination (2 : ℤ) ^ m * hk2⟩⟩

theorem t200_twist_fix_uv (hm : 1 ≤ m) {y : ℤ} (hy : y = -1 ∨ y = -1 + 2 ^ (m + 1)) :
    ∃ d : Torus (StrothTypeIndex.t200 m).k,
      y • (StrothTypeIndex.t200 m).action.φuv d = d ∧ (2 ^ (m + 1) : ℤ) • d ≠ 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rcases hy with rfl | rfl
  · refine ⟨Torus.ofInt _ ![0, 1, -1], ?_, ?_⟩
    · rw [t200_φuv_vec, t200_zsmul_vec, t200_vec_eq_iff]
      exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
    · intro h
      rw [t200_zsmul_vec, t200_vec_eq_zero_iff] at h
      exact not_two_pow_succ_dvd_mul_odd (m' + 1 + 1) (by norm_num) h.2.1
  · refine ⟨Torus.ofInt _ ![0, 1, -1 + 2 ^ (m' + 1)], ?_, ?_⟩
    · rw [t200_φuv_vec, t200_zsmul_vec, t200_vec_eq_iff]
      exact ⟨⟨1 - 2 * 2 ^ (m' + 1), by ring⟩, ⟨1 - 2 ^ (m' + 1), by ring⟩,
        ⟨-(2 ^ m'), by ring⟩⟩
    · intro h
      rw [t200_zsmul_vec, t200_vec_eq_zero_iff] at h
      exact not_two_pow_succ_dvd_mul_odd (m' + 1 + 1) (by norm_num) h.2.1

theorem t200_twist_fix_t (hm : 1 ≤ m) {y : ℤ} (hy : y = -1 ∨ y = -1 + 2 ^ (m + 1)) :
    ∃ d : Torus (StrothTypeIndex.t200 m).k,
      y • (StrothTypeIndex.t200 m).action.φt d = d ∧ (2 ^ (m + 1) : ℤ) • d ≠ 0 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rcases hy with rfl | rfl
  · refine ⟨Torus.ofInt _ ![0, 1, 0], ?_, ?_⟩
    · rw [t200_φt_vec, t200_zsmul_vec, t200_vec_eq_iff]
      exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
    · intro h
      rw [t200_zsmul_vec, t200_vec_eq_zero_iff] at h
      exact not_two_pow_succ_dvd_mul_odd (m' + 1 + 1) (by norm_num) h.2.1
  · refine ⟨Torus.ofInt _ ![0, 1, 2 ^ (m' + 1)], ?_, ?_⟩
    · rw [t200_φt_vec, t200_zsmul_vec, t200_vec_eq_iff]
      exact ⟨⟨2 * 2 ^ (m' + 1) - 1, by ring⟩, ⟨2 ^ (m' + 1), by ring⟩, ⟨2 ^ m', by ring⟩⟩
    · intro h
      rw [t200_zsmul_vec, t200_vec_eq_zero_iff] at h
      exact not_two_pow_succ_dvd_mul_odd (m' + 1 + 1) (by norm_num) h.2.1

end Stroth34T200

end CFSG.CGT.Stroth77
