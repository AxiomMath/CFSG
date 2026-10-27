module

public import CFSG.CGT.Stroth77.Section43Fus
public import CFSG.CGT.Stroth77.Stroth34Layer

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core

namespace Stroth32H1

variable {m : ℕ}

theorem t100_exists_vec (x : Torus (StrothTypeIndex.t100 m).k) :
    ∃ a b c : ℤ, x = Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  refine ⟨v 0, v 1, v 2, ?_⟩
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t100_vec_eq_iff (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] = Torus.ofInt _ ![a', b', c'] ↔
      (2 : ℤ) ^ m ∣ a' - a ∧ (2 : ℤ) ^ (m + 1) ∣ b' - b ∧ (2 : ℤ) ^ (m + 1) ∣ c' - c :=
  t100_ofInt_eq_iff ![a, b, c] ![a', b', c']

theorem t100_vec_eq_zero_iff (a b c : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] = 0 ↔
      (2 : ℤ) ^ m ∣ a ∧ (2 : ℤ) ^ (m + 1) ∣ b ∧ (2 : ℤ) ^ (m + 1) ∣ c :=
  t100_ofInt_eq_zero_iff ![a, b, c]

theorem t100_add_vec (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] + Torus.ofInt _ ![a', b', c'] =
      Torus.ofInt _ ![a + a', b + b', c + c'] := by
  rw [← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t100_sub_vec (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] - Torus.ofInt _ ![a', b', c'] =
      Torus.ofInt _ ![a - a', b - b', c - c'] := by
  rw [← Torus.ofInt_sub]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t100_neg_vec (a b c : ℤ) :
    -Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] = Torus.ofInt _ ![-a, -b, -c] := by
  rw [← Torus.ofInt_neg]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t100_zsmul_vec (z a b c : ℤ) :
    z • Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] =
      Torus.ofInt _ ![z * a, z * b, z * c] := by
  rw [← Torus.ofInt_zsmul]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t100_φuv_vec (a b c : ℤ) :
    (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![-3 * a + 2 * b + 2 * c, -2 * a + b + 2 * c, -2 * a + 2 * b + c] :=
  t100_φuv ![a, b, c]

theorem t100_φt_vec (a b c : ℤ) :
    (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a - 2 * c, 2 * a - b - 2 * c, -c] :=
  t100_φt ![a, b, c]

theorem t100_φu_vec (a b c : ℤ) :
    (StrothTypeIndex.t100 m).action.φu (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a, c, b] :=
  t100_φu ![a, b, c]

theorem t100_φρ_vec (a b c : ℤ) :
    (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a - 2 * c, -c, b - c] :=
  t100_φρ ![a, b, c]

theorem t100_c_eq_ofInt :
    (Torus.c : Torus (StrothTypeIndex.t100 m).k) = Torus.ofInt _ ![1, 0, 0] := by
  show gen _ 0 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem t100_a_eq_ofInt :
    (Torus.a : Torus (StrothTypeIndex.t100 m).k) = Torus.ofInt _ ![0, 1, 0] := by
  show gen _ 1 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem t100_b_eq_ofInt :
    (Torus.b : Torus (StrothTypeIndex.t100 m).k) = Torus.ofInt _ ![0, 0, 1] := by
  show gen _ 2 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem t100_cocycle_ints (x y : Fin 3 → ℤ)
    (h1 : Torus.ofInt (StrothTypeIndex.t100 m).k x +
      (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ x) = 0)
    (h2 : Torus.ofInt (StrothTypeIndex.t100 m).k y +
      (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ y) = 0)
    (h3 : Torus.ofInt (StrothTypeIndex.t100 m).k x +
      (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ y) =
      Torus.ofInt _ y + (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ x)) :
    ∃ κ₁ κ₂ κ₃ : ℤ, x 1 + x 2 = x 0 + 2 ^ m * κ₁ ∧ y 2 = y 0 + 2 ^ m * κ₂ ∧
      y 0 - y 1 = x 2 + 2 ^ m * κ₃ := by
  simp only [t100_φuv, t100_φt, ← Torus.ofInt_add] at h1 h2 h3
  rw [t100_ofInt_eq_zero_iff] at h1 h2
  rw [t100_ofInt_eq_iff] at h3
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3
  obtain ⟨-, ⟨k1, e1⟩, -⟩ := h1
  obtain ⟨-, ⟨k2, e2⟩, -⟩ := h2
  obtain ⟨-, -, ⟨k3, e3⟩⟩ := h3
  refine ⟨k1, -k2, k3, ?_, ?_, ?_⟩
  · have h : 2 * (x 1 + x 2) = 2 * (x 0 + 2 ^ m * k1) := by linear_combination e1
    exact mul_left_cancel₀ two_ne_zero h
  · have h : 2 * y 2 = 2 * (y 0 + 2 ^ m * -k2) := by linear_combination -e2
    exact mul_left_cancel₀ two_ne_zero h
  · have h : 2 * (y 0 - y 1) = 2 * (x 2 + 2 ^ m * k3) := by linear_combination e3
    exact mul_left_cancel₀ two_ne_zero h

theorem t100_cocycle_of_ints (x y : Fin 3 → ℤ) {κ₁ κ₂ κ₃ : ℤ}
    (e1 : x 1 + x 2 = x 0 + 2 ^ m * κ₁) (e2 : y 2 = y 0 + 2 ^ m * κ₂)
    (e3 : y 0 - y 1 = x 2 + 2 ^ m * κ₃) :
    Torus.ofInt (StrothTypeIndex.t100 m).k x +
        (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ x) = 0 ∧
      Torus.ofInt (StrothTypeIndex.t100 m).k y +
        (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ y) = 0 ∧
      Torus.ofInt (StrothTypeIndex.t100 m).k x +
          (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ y) =
        Torus.ofInt _ y + (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ x) := by
  simp only [t100_φuv, t100_φt, ← Torus.ofInt_add]
  rw [t100_ofInt_eq_zero_iff, t100_ofInt_eq_zero_iff, t100_ofInt_eq_iff]
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  exact ⟨⟨⟨2 * κ₁, by linear_combination 2 * e1⟩, ⟨κ₁, by linear_combination 2 * e1⟩,
      ⟨κ₁, by linear_combination 2 * e1⟩⟩,
    ⟨⟨-2 * κ₂, by linear_combination -2 * e2⟩, ⟨-κ₂, by linear_combination -2 * e2⟩,
      ⟨0, by ring⟩⟩,
    ⟨2 * (κ₃ - κ₂), by linear_combination -2 * e2 + 2 * e3⟩,
    ⟨-κ₁ - κ₂, by linear_combination -2 * e1 - 2 * e2⟩, ⟨κ₃, by linear_combination 2 * e3⟩⟩

theorem t100_cob_uv_vec (a b c : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] -
        (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![4 * a - 2 * b - 2 * c, 2 * a - 2 * c, 2 * a - 2 * b] := by
  rw [t100_φuv_vec, t100_sub_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t100_cob_t_vec (a b c : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] -
        (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![2 * c, -2 * a + 2 * b + 2 * c, 2 * c] := by
  rw [t100_φt_vec, t100_sub_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t100_cob_add_of_even (hm : 1 ≤ m) (x y : Fin 3 → ℤ) {κ₁ κ₂ κ₃ : ℤ}
    (e1 : x 1 + x 2 = x 0 + 2 ^ m * κ₁) (e2 : y 2 = y 0 + 2 ^ m * κ₂)
    (e3 : y 0 - y 1 = x 2 + 2 ^ m * κ₃) (hx1 : Even (x 1)) (hx2 : Even (x 2))
    (hy0 : Even (y 0)) :
    ∃ d : Torus (StrothTypeIndex.t100 m).k,
      Torus.ofInt (StrothTypeIndex.t100 m).k x = d - (StrothTypeIndex.t100 m).action.φuv d ∧
        Torus.ofInt (StrothTypeIndex.t100 m).k y = d - (StrothTypeIndex.t100 m).action.φt d +
          Torus.ofInt _ ![0, 2 ^ m * (κ₂ + κ₃), 0] := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨X₁, hX₁⟩ := hx1
  obtain ⟨X₂, hX₂⟩ := hx2
  obtain ⟨Y₀, hY₀⟩ := hy0
  refine ⟨Torus.ofInt _ ![X₁ + Y₀ + 2 ^ n * κ₂, X₁ - X₂ + Y₀ + 2 ^ n * κ₂, Y₀ + 2 ^ n * κ₂],
    ?_, ?_⟩
  · rw [t100_cob_uv_vec, t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨κ₁, by linear_combination e1 - hX₁ - hX₂⟩, ⟨0, by linear_combination -hX₁⟩,
      ⟨0, by linear_combination -hX₂⟩⟩
  · rw [t100_cob_t_vec, t100_add_vec, t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨κ₂, by linear_combination -hY₀⟩, ⟨κ₂ + κ₃, by linear_combination e3 - hY₀ + hX₂⟩,
      ⟨0, by linear_combination -e2 - hY₀⟩⟩

theorem t100_cob_of_even (hm : 1 ≤ m) (x y : Fin 3 → ℤ) {κ₁ κ₂ κ₃ : ℤ}
    (e1 : x 1 + x 2 = x 0 + 2 ^ m * κ₁) (e2 : y 2 = y 0 + 2 ^ m * κ₂)
    (e3 : y 0 - y 1 = x 2 + 2 ^ m * κ₃) (hx1 : Even (x 1)) (hx2 : Even (x 2))
    (hy0 : Even (y 0)) (hκ : Even (κ₂ + κ₃)) :
    ∃ d : Torus (StrothTypeIndex.t100 m).k,
      Torus.ofInt (StrothTypeIndex.t100 m).k x = d - (StrothTypeIndex.t100 m).action.φuv d ∧
        Torus.ofInt (StrothTypeIndex.t100 m).k y = d - (StrothTypeIndex.t100 m).action.φt d := by
  obtain ⟨d, h1, h2⟩ := t100_cob_add_of_even hm x y e1 e2 e3 hx1 hx2 hy0
  refine ⟨d, h1, ?_⟩
  obtain ⟨K, hK⟩ := hκ
  have h0 : Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 2 ^ m * (κ₂ + κ₃), 0] = 0 := by
    rw [t100_vec_eq_zero_iff]
    exact ⟨dvd_zero _, ⟨K, by rw [hK]; ring⟩, dvd_zero _⟩
  rw [h2, h0, add_zero]

theorem t100_even_of_cob (hm : 1 ≤ m) (x y : Fin 3 → ℤ) {κ₂ κ₃ : ℤ}
    (e2 : y 2 = y 0 + 2 ^ m * κ₂) (e3 : y 0 - y 1 = x 2 + 2 ^ m * κ₃)
    (d : Torus (StrothTypeIndex.t100 m).k)
    (h1 : Torus.ofInt (StrothTypeIndex.t100 m).k x = d - (StrothTypeIndex.t100 m).action.φuv d)
    (h2 : Torus.ofInt (StrothTypeIndex.t100 m).k y = d - (StrothTypeIndex.t100 m).action.φt d) :
    Even (x 1) ∧ Even (x 2) ∧ Even (y 0) ∧ Even (κ₂ + κ₃) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨a, b, c, rfl⟩ := t100_exists_vec d
  rw [t100_cob_uv_vec, t100_ofInt_eq_iff] at h1
  rw [t100_cob_t_vec, t100_ofInt_eq_iff] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h2
  obtain ⟨-, ⟨j1, f1⟩, ⟨j2, f2⟩⟩ := h1
  obtain ⟨⟨i0, g0⟩, ⟨i1, g1⟩, ⟨i2, g2⟩⟩ := h2
  have hκ : 2 ^ (n + 1) * (κ₂ + κ₃) = 2 ^ (n + 1) * ((i1 + j2 - i2) + (i1 + j2 - i2)) := by
    linear_combination -e2 - e3 - g2 + g1 + f2
  exact ⟨⟨a - c - 2 ^ (n + 1) * j1, by linear_combination -f1⟩,
    ⟨a - b - 2 ^ (n + 1) * j2, by linear_combination -f2⟩,
    ⟨c - 2 ^ n * i0, by linear_combination -g0⟩,
    ⟨i1 + j2 - i2, mul_left_cancel₀ (pow_ne_zero _ two_ne_zero) hκ⟩⟩

theorem t100_not_rho_triv (hm : 1 ≤ m) :
    ¬ ∀ ruv rt : Torus (StrothTypeIndex.t100 m).k,
      ruv + (StrothTypeIndex.t100 m).action.φuv ruv = 0 →
      rt + (StrothTypeIndex.t100 m).action.φt rt = 0 →
      ruv + (StrothTypeIndex.t100 m).action.φuv rt =
        rt + (StrothTypeIndex.t100 m).action.φt ruv →
      ∃ d₀ : Torus (StrothTypeIndex.t100 m).k,
        (StrothTypeIndex.t100 m).action.φρ (ruv + (StrothTypeIndex.t100 m).action.φuv rt) =
            ruv - d₀ + (StrothTypeIndex.t100 m).action.φuv d₀ ∧
          (StrothTypeIndex.t100 m).action.φρ ruv =
            rt - d₀ + (StrothTypeIndex.t100 m).action.φt d₀ := by
  intro hρ
  obtain ⟨c1, c2, c3⟩ := t100_cocycle_of_ints (m := m) ![1, 1, 0] ![0, 0, 0] (κ₁ := 0) (κ₂ := 0)
    (κ₃ := 0) (by simp) (by simp) (by simp)
  obtain ⟨d₀, s1, s2⟩ := hρ _ _ c1 c2 c3
  have hl1 : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![1, 1, 0] +
      (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ ![0, 0, 0])) =
        Torus.ofInt _ ![1, 0, 1] := by
    rw [t100_φuv_vec, t100_add_vec, t100_φρ_vec, t100_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  have hl2 : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![1, 1, 0]) =
      Torus.ofInt _ ![1, 0, 1] := by
    rw [t100_φρ_vec, t100_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  have hz : Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 0] = 0 := by
    rw [t100_vec_eq_zero_iff]
    simp
  have hd : Torus.ofInt (StrothTypeIndex.t100 m).k ![0, -1, 1] =
      Torus.ofInt _ ![1, 0, 1] - Torus.ofInt _ ![1, 1, 0] := by
    rw [t100_sub_vec, t100_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  rw [hl1] at s1
  rw [hl2, hz] at s2
  obtain ⟨⟨r, hr⟩, -⟩ := t100_even_of_cob hm ![0, -1, 1] ![1, 0, 1] (κ₂ := 0) (κ₃ := 0)
    (by simp) (by simp) (-d₀) (by rw [hd, s1, map_neg]; abel) (by rw [s2, map_neg]; abel)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hr
  omega

theorem t100_u_triv_of_rho (hm : 1 ≤ m) (ruv rt : Torus (StrothTypeIndex.t100 m).k)
    (h1 : ruv + (StrothTypeIndex.t100 m).action.φuv ruv = 0)
    (h2 : rt + (StrothTypeIndex.t100 m).action.φt rt = 0)
    (h3 : ruv + (StrothTypeIndex.t100 m).action.φuv rt =
      rt + (StrothTypeIndex.t100 m).action.φt ruv)
    (d₀ : Torus (StrothTypeIndex.t100 m).k)
    (s1 : (StrothTypeIndex.t100 m).action.φρ (ruv + (StrothTypeIndex.t100 m).action.φuv rt) =
      ruv - d₀ + (StrothTypeIndex.t100 m).action.φuv d₀)
    (s2 : (StrothTypeIndex.t100 m).action.φρ ruv =
      rt - d₀ + (StrothTypeIndex.t100 m).action.φt d₀) :
    ∃ d : Torus (StrothTypeIndex.t100 m).k,
      (StrothTypeIndex.t100 m).action.φu ruv = ruv - d + (StrothTypeIndex.t100 m).action.φuv d ∧
        (StrothTypeIndex.t100 m).action.φu (ruv + (StrothTypeIndex.t100 m).action.φuv rt) =
          rt - d + (StrothTypeIndex.t100 m).action.φt d := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt ruv
  obtain ⟨y, rfl⟩ := Torus.exists_ofInt rt
  obtain ⟨p, rfl⟩ := Torus.exists_ofInt d₀
  obtain ⟨κ₁, κ₂, κ₃, e1, e2, e3⟩ := t100_cocycle_ints x y h1 h2 h3
  simp only [t100_φρ, t100_φt, ← Torus.ofInt_add, ← Torus.ofInt_sub] at s2
  rw [t100_ofInt_eq_iff] at s2
  simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at s2
  obtain ⟨-, ⟨σ1, f1⟩, ⟨σ2, f2⟩⟩ := s2
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hY : y 0 = 2 * (2 ^ n * κ₃ + p 1 - p 0 + p 2 + 2 ^ (n + 1) * σ1) := by
    linear_combination f1 + e3
  obtain ⟨W, hX⟩ : ∃ W, x 2 - x 1 = 2 * W :=
    ⟨2 ^ (n + 1) * σ2 - (2 ^ n * κ₃ + p 1 - p 0 + p 2 + 2 ^ (n + 1) * σ1) - 2 ^ n * κ₂ + p 2,
      by linear_combination f2 - e2 - hY⟩
  obtain ⟨d', hd1, hd2⟩ := t100_cob_of_even (by omega) ![0, x 2 - x 1, x 1 - x 2]
    ![x 0 - 4 * y 0 + 2 * y 1 + 2 * y 2, x 2 - 2 * y 0 + y 1 + y 2, x 1 - 2 * y 0 + y 1 + y 2]
    (κ₁ := 0) (κ₂ := κ₁ + κ₃ - κ₂) (κ₃ := -(κ₁ + κ₃ - κ₂))
    (show x 2 - x 1 + (x 1 - x 2) = 0 + 2 ^ (n + 1) * 0 by ring)
    (show x 1 - 2 * y 0 + y 1 + y 2 =
        x 0 - 4 * y 0 + 2 * y 1 + 2 * y 2 + 2 ^ (n + 1) * (κ₁ + κ₃ - κ₂) by
      linear_combination e1 - e2 + e3)
    (show x 0 - 4 * y 0 + 2 * y 1 + 2 * y 2 - (x 2 - 2 * y 0 + y 1 + y 2) =
        x 1 - x 2 + 2 ^ (n + 1) * -(κ₁ + κ₃ - κ₂) by
      linear_combination -e1 + e2 - e3)
    (show Even (x 2 - x 1) from ⟨W, by linear_combination hX⟩)
    (show Even (x 1 - x 2) from ⟨-W, by linear_combination -hX⟩)
    (show Even (x 0 - 4 * y 0 + 2 * y 1 + 2 * y 2) from
      ⟨x 2 - W - 2 ^ n * κ₁ - 2 * y 0 + y 1 + y 2, by linear_combination -e1 - hX⟩)
    ⟨0, by ring⟩
  have hneg : ∀ (A B : Torus (StrothTypeIndex.t100 (n + 1)).k)
      (φ : Torus (StrothTypeIndex.t100 (n + 1)).k →+ Torus (StrothTypeIndex.t100 (n + 1)).k),
      A - -B + φ (-B) = A + (B - φ B) := fun A B φ => by
    rw [map_neg]
    abel
  refine ⟨-d', ?_, ?_⟩
  · rw [hneg, ← hd1, ← Torus.ofInt_add, t100_φu, t100_ofInt_eq_iff]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  · rw [hneg, ← hd2, ← Torus.ofInt_add, t100_φuv, ← Torus.ofInt_add, t100_φu, t100_ofInt_eq_iff]
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

end Stroth32H1

open Stroth32H1

namespace StrothWeakTypeData

section Coord

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t100 m))

theorem t100_c_eq : (dD.c : G) = dD.ofT (Torus.ofInt _ ![1, 0, 0]) := by
  rw [← t100_c_eq_ofInt]; rfl

theorem t100_a_eq : (dD.a : G) = dD.ofT (Torus.ofInt _ ![0, 1, 0]) := by
  rw [← t100_a_eq_ofInt]; rfl

theorem t100_b_eq : (dD.b : G) = dD.ofT (Torus.ofInt _ ![0, 0, 1]) := by
  rw [← t100_b_eq_ofInt]; rfl

end Coord

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m))

theorem t100_even_of_mem (hm : 1 ≤ m) {d : G} (hd : d ∈ D) (x y : Fin 3 → ℤ)
    (hx : crdT dD.e (d⁻¹ * dD.uv * d * dD.uv⁻¹) = Torus.ofInt _ x)
    (hy : crdT dD.e (d⁻¹ * dD.t * d * dD.t⁻¹) = Torus.ofInt _ y) {κ₂ κ₃ : ℤ}
    (e2 : y 2 = y 0 + 2 ^ m * κ₂) (e3 : y 0 - y 1 = x 2 + 2 ^ m * κ₃) :
    Even (x 1) ∧ Even (x 2) ∧ Even (y 0) ∧ Even (κ₂ + κ₃) := by
  refine t100_even_of_cob hm x y e2 e3 (-crdT dD.e d) ?_ ?_
  · rw [← hx, (dD.crdT_cocycle_of_mem_uv hd).2, map_neg]
    abel
  · rw [← hy, (dD.crdT_cocycle_of_mem_t hd).2, map_neg]
    abel

end StrothWeakTypeData

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}

theorem mem_of_cocycle_cob_add_E {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}
    (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e : G} (he : e ∈ hS.R)
    (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D) (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D)
    (c₀ ω₁ ω₂ : Torus τ.k) (hω₁ : dD.ofT ω₁ ∈ F.E) (hω₂ : dD.ofT ω₂ ∈ F.E)
    (h1 : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) = c₀ - τ.action.φuv c₀ + ω₁)
    (h2 : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) = c₀ - τ.action.φt c₀ + ω₂) : e ∈ D := by
  have hd := dD.ofT_mem c₀
  obtain ⟨huv', cuv⟩ := crdT_conj_mul dD.e dD.uv_mem dD.uv_sq dD.uv_conj huv hd
  obtain ⟨ht', ct⟩ := crdT_conj_mul dD.e dD.t_mem dD.t_sq dD.t_conj ht hd
  rw [dD.crdT_ofT, h1, show c₀ - τ.action.φuv c₀ + ω₁ - c₀ + τ.action.φuv c₀ = ω₁ by abel]
    at cuv
  rw [dD.crdT_ofT, h2, show c₀ - τ.action.φt c₀ + ω₂ - c₀ + τ.action.φt c₀ = ω₂ by abel] at ct
  have hR : e * dD.ofT c₀ ∈ hS.R := mul_mem he (hS.D_le_R hd)
  have key : e * dD.ofT c₀ ∈ D := by
    refine h.mem_of_conj_mem_E (hS.R_le_S hR) (hS.R_le_centralizer_omega hR) ?_ ?_
    · rw [← dD.ofT_crdT huv', cuv]
      exact hω₁
    · rw [← dD.ofT_crdT ht', ct]
      exact hω₂
  simpa using mul_mem key (inv_mem hd)

variable {m : ℕ} {dD : StrothWeakTypeData D (.t100 m)}

theorem t100_ofT_mem_E (h : F.IsD D dD) (hm : 1 ≤ m) (v : Fin 3 → ℤ) (h0 : (2 : ℤ) ^ m ∣ v 0)
    (h1 : (2 : ℤ) ^ m ∣ v 1) (h2 : (2 : ℤ) ^ m ∣ v 2) :
    dD.ofT (Torus.ofInt (StrothTypeIndex.t100 m).k v) ∈ F.E := by
  obtain ⟨i0, hi0⟩ := h0
  obtain ⟨i1, hi1⟩ := h1
  obtain ⟨i2, hi2⟩ := h2
  obtain ⟨-, ha, hb⟩ := h.t100_omega_eq hm
  have hA : dD.ofT (Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 2 ^ m, 0]) =
      ((F.dA.a : F.A) : G) ^ 2 := by
    rw [← ha, dD.t100_a_eq,
      ← zpow_natCast (dD.ofT (Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0])),
      ← dD.ofT_zsmul, t100_zsmul_vec]
    congr 1
    rw [t100_vec_eq_iff]
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> simp
  have hB : dD.ofT (Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 2 ^ m]) =
      ((F.dA.b : F.A) : G) ^ 2 := by
    rw [← hb, dD.t100_b_eq,
      ← zpow_natCast (dD.ofT (Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 1])),
      ← dD.ofT_zsmul, t100_zsmul_vec]
    congr 1
    rw [t100_vec_eq_iff]
    refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> simp
  have hv : Torus.ofInt (StrothTypeIndex.t100 m).k v =
      i1 • Torus.ofInt _ ![0, 2 ^ m, 0] + i2 • Torus.ofInt _ ![0, 0, 2 ^ m] := by
    rw [t100_zsmul_vec, t100_zsmul_vec, t100_add_vec, t100_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨-i0, by linear_combination -hi0⟩, ⟨0, by linear_combination -hi1⟩,
      ⟨0, by linear_combination -hi2⟩⟩
  rw [hv, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, hA, hB]
  exact mul_mem (zpow_mem F.a_sq_mem_E _) (zpow_mem F.b_sq_mem_E _)

theorem t100_mem_of_even (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e : G} (he : e ∈ hS.R1 dD.uv dD.t) (x y : Fin 3 → ℤ)
    (hx : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) = Torus.ofInt _ x)
    (hy : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) = Torus.ofInt _ y)
    (hx1 : Even (x 1)) (hx2 : Even (x 2)) (hy0 : Even (y 0)) : e ∈ D := by
  obtain ⟨heR, huv, ht⟩ := he
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  rw [hx] at c1
  rw [hy] at c2
  rw [hx, hy] at c3
  obtain ⟨κ₁, κ₂, κ₃, e1, e2, e3⟩ := t100_cocycle_ints x y c1 c2 c3
  obtain ⟨d, h1, h2⟩ := t100_cob_add_of_even hm x y e1 e2 e3 hx1 hx2 hy0
  refine h.mem_of_cocycle_cob_add_E hS heR huv ht d 0 _ ?_
    (h.t100_ofT_mem_E hm ![0, 2 ^ m * (κ₂ + κ₃), 0] (dvd_zero _) (dvd_mul_right _ _)
      (dvd_zero _)) ?_ ?_
  · rw [dD.ofT_zero]
    exact one_mem _
  · rw [hx, h1, add_zero]
  · rw [hy, h2]

theorem t100_conj_u_mul_inv_mem (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) {e : G} (he : e ∈ hS.R1 dD.uv dD.t) (hpe : hS.proj dD.ρ e * e⁻¹ ∈ D) :
    dD.u⁻¹ * e * dD.u * e⁻¹ ∈ D := by
  obtain ⟨heR, huv, ht⟩ := he
  have hd₀ : e⁻¹ * hS.proj dD.ρ e ∈ D := by
    have := (Subgroup.mem_normalizer_iff''.mp (hS.R_le_normalizer heR) _).mp hpe
    convert this using 1
    group
  obtain ⟨s1, s2⟩ := h.rho_stable_crd hS heR huv ht hd₀ (by group)
  obtain ⟨c1, c2, c3⟩ := cocycle_uv_t dD.e dD.uv_sq dD.t_sq dD.uv_comm_t dD.uv_mem dD.t_mem
    dD.uv_conj dD.t_conj huv ht
  obtain ⟨d, w1, w2⟩ := t100_u_triv_of_rho hm _ _ c1 c2 c3 _ s1 s2
  obtain ⟨puv, pt, p1, p2⟩ := cocycle_conj_u hS huv ht
  refine h.mul_inv_mem_of_cocycle_cob hS ⟨h.conj_u_mem_R hS heR, puv, pt⟩ ⟨heR, huv, ht⟩ (-d)
    ?_ ?_
  · rw [p1, w1, map_neg]; abel
  · rw [p2, w2, map_neg]; abel

end StrothFrame.IsD

end CFSG.CGT.Stroth77
