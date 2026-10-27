module

public import CFSG.CGT.Stroth77.Section44Core
public import CFSG.CGT.Stroth77.Stroth34T200H1
public import CFSG.CGT.Stroth77.Stroth34T200Facts

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T201

open Stroth44Core

variable {m : ℕ}

theorem t201_exists_vec (x : Torus (StrothTypeIndex.t201 m).k) :
    ∃ a b c : ℤ, x = Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt x
  refine ⟨v 0, v 1, v 2, ?_⟩
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t201_vec_eq_iff (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] = Torus.ofInt _ ![a', b', c'] ↔
      (2 : ℤ) ^ m ∣ a' - a ∧ (2 : ℤ) ^ (m + 2) ∣ b' - b ∧ (2 : ℤ) ^ (m + 2) ∣ c' - c :=
  t201_ofInt_eq_iff ![a, b, c] ![a', b', c']

theorem t201_vec_eq_zero_iff (a b c : ℤ) :
    Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] = 0 ↔
      (2 : ℤ) ^ m ∣ a ∧ (2 : ℤ) ^ (m + 2) ∣ b ∧ (2 : ℤ) ^ (m + 2) ∣ c := by
  rw [← Torus.ofInt_zero, t201_ofInt_eq_iff]
  simp

theorem t201_add_vec (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] + Torus.ofInt _ ![a', b', c'] =
      Torus.ofInt _ ![a + a', b + b', c + c'] := by
  rw [← Torus.ofInt_add]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t201_sub_vec (a b c a' b' c' : ℤ) :
    Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] - Torus.ofInt _ ![a', b', c'] =
      Torus.ofInt _ ![a - a', b - b', c - c'] := by
  rw [← Torus.ofInt_sub]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t201_neg_vec (a b c : ℤ) :
    -Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] = Torus.ofInt _ ![-a, -b, -c] := by
  rw [← Torus.ofInt_neg]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t201_zsmul_vec (z a b c : ℤ) :
    z • Torus.ofInt (StrothTypeIndex.t201 m).k ![a, b, c] =
      Torus.ofInt _ ![z * a, z * b, z * c] := by
  rw [← Torus.ofInt_zsmul]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t201_φuv_vec (a b c : ℤ) :
    (StrothTypeIndex.t201 m).action.φuv (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![-3 * a + b + c,
        -4 * a + b + (2 + 3 * 2 ^ (m + 1) + 2 ^ (m + 1) * 2 ^ (m + 1)) * c,
        -4 * a + (2 + 2 ^ (m + 1)) * b + c] :=
  t201_φuv ![a, b, c]

theorem t201_φt_vec (a b c : ℤ) :
    (StrothTypeIndex.t201 m).action.φt (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a - (1 + 2 ^ (m + 1)) * c,
        4 * a + (2 ^ (m + 1) - 1) * b - (2 + 2 ^ (m + 1)) * c, -(1 + 2 ^ (m + 1)) * c] :=
  t201_φt ![a, b, c]

theorem t201_φu_vec (a b c : ℤ) :
    (StrothTypeIndex.t201 m).action.φu (Torus.ofInt _ ![a, b, c]) = Torus.ofInt _ ![a, c, b] :=
  t201_φu ![a, b, c]

theorem t201_φρ_vec (a b c : ℤ) :
    (StrothTypeIndex.t201 m).action.φρ (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a - c, -c, b - c] :=
  t201_φρ ![a, b, c]

theorem rho_triv_of_intertwine {A : Type*} [AddCommGroup A] {U0 T0 P0 U1 T1 P1 g h : A →+ A}
    (hgh : ∀ x, g (h x) = x) (hhg : ∀ x, h (g x) = x)
    (hU : ∀ x, g (U0 x) = U1 (g x)) (hT : ∀ x, g (T0 x) = T1 (g x))
    (hP : ∀ x, g (P0 x) = P1 (g x))
    (h0 : ∀ ruv rt : A, ruv + U0 ruv = 0 → rt + T0 rt = 0 → ruv + U0 rt = rt + T0 ruv →
      ∃ d₀ : A, P0 (ruv + U0 rt) = ruv - d₀ + U0 d₀ ∧ P0 ruv = rt - d₀ + T0 d₀)
    (ruv rt : A) (h1 : ruv + U1 ruv = 0) (h2 : rt + T1 rt = 0)
    (h3 : ruv + U1 rt = rt + T1 ruv) :
    ∃ d₀ : A, P1 (ruv + U1 rt) = ruv - d₀ + U1 d₀ ∧ P1 ruv = rt - d₀ + T1 d₀ := by
  have hU' : ∀ x, h (U1 x) = U0 (h x) := fun x => by
    have := congrArg h (hU (h x))
    rw [hhg, hgh] at this
    exact this.symm
  have hT' : ∀ x, h (T1 x) = T0 (h x) := fun x => by
    have := congrArg h (hT (h x))
    rw [hhg, hgh] at this
    exact this.symm
  obtain ⟨d, e1, e2⟩ := h0 (h ruv) (h rt)
    (by rw [← hU', ← map_add, h1, map_zero])
    (by rw [← hT', ← map_add, h2, map_zero])
    (by rw [← hU', ← hT', ← map_add, ← map_add, h3])
  refine ⟨g d, ?_, ?_⟩
  · simpa only [hP, map_add, map_sub, hgh, hU] using congrArg g e1
  · simpa only [hP, map_add, map_sub, hgh, hT] using congrArg g e2

abbrev U0 (m : ℕ) : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k :=
  matAct (StrothTypeIndex.t201 m).k Type200.uvM (Type200.compat_uv m)

abbrev T0 (m : ℕ) : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k :=
  matAct (StrothTypeIndex.t201 m).k Type200.tM (Type200.compat_t m)

abbrev P0 (m : ℕ) : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k :=
  matAct (StrothTypeIndex.t201 m).k Type200.ρM (Type200.compat_rho m)

theorem U0_vec (a b c : ℤ) :
    U0 m (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![-3 * a + b + c, -4 * a + b + 2 * c, -4 * a + 2 * b + c] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t201 m).k) Type200.uvM (Type200.compat_uv m)
    ![a, b, c]
  rw [Type200.uvM_mulVec] at h
  exact h

theorem T0_vec (a b c : ℤ) :
    T0 m (Torus.ofInt _ ![a, b, c]) = Torus.ofInt _ ![a - c, 4 * a - b - 2 * c, -c] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t201 m).k) Type200.tM (Type200.compat_t m)
    ![a, b, c]
  rw [Type200.tM_mulVec] at h
  exact h

theorem P0_vec (a b c : ℤ) :
    P0 m (Torus.ofInt _ ![a, b, c]) = Torus.ofInt _ ![a - c, -c, b - c] := by
  have h := matAct_ofInt (k := (StrothTypeIndex.t201 m).k) Type200.ρM (Type200.compat_rho m)
    ![a, b, c]
  rw [Type200.ρM_mulVec] at h
  exact h

theorem t200_rho_triv_on (ruv rt : Torus (StrothTypeIndex.t201 m).k)
    (h1 : ruv + U0 m ruv = 0) (h2 : rt + T0 m rt = 0) (h3 : ruv + U0 m rt = rt + T0 m ruv) :
    ∃ d₀ : Torus (StrothTypeIndex.t201 m).k,
      P0 m (ruv + U0 m rt) = ruv - d₀ + U0 m d₀ ∧ P0 m ruv = rt - d₀ + T0 m d₀ :=
  Stroth34T200.t200_rho_triv (m := m) ruv rt h1 h2 h3

abbrev gI (m : ℕ) : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k :=
  AddMonoidHom.id _ + (2 ^ m : ℤ) • (StrothTypeIndex.t201 m).action.φρ

abbrev hI (m : ℕ) : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k :=
  AddMonoidHom.id _ - (2 ^ m : ℤ) • (StrothTypeIndex.t201 m).action.φρ +
    (2 ^ m * 2 ^ m : ℤ) •
      ((StrothTypeIndex.t201 m).action.φρ).comp (StrothTypeIndex.t201 m).action.φρ

theorem gI_vec (a b c : ℤ) :
    gI m (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a + 2 ^ m * (a - c), b + 2 ^ m * -c, c + 2 ^ m * (b - c)] := by
  simp only [AddMonoidHom.add_apply, AddMonoidHom.id_apply, AddMonoidHom.smul_apply,
    t201_φρ_vec, t201_zsmul_vec, t201_add_vec]

theorem hI_vec (a b c : ℤ) :
    hI m (Torus.ofInt _ ![a, b, c]) =
      Torus.ofInt _ ![a - 2 ^ m * (a - c) + 2 ^ m * 2 ^ m * (a - c - (b - c)),
        b - 2 ^ m * -c + 2 ^ m * 2 ^ m * -(b - c),
        c - 2 ^ m * (b - c) + 2 ^ m * 2 ^ m * (-c - (b - c))] := by
  simp only [AddMonoidHom.add_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, t201_φρ_vec, t201_zsmul_vec, t201_add_vec,
    t201_sub_vec]

theorem gI_hI (hm : 1 ≤ m) (x : Torus (StrothTypeIndex.t201 m).k) : gI m (hI m x) = x := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [hI_vec, gI_vec, t201_vec_eq_iff]
  exact ⟨⟨-(4 * (2 ^ j) ^ 2 * a), by ring⟩, ⟨-((2 ^ j) ^ 2 * b), by ring⟩,
    ⟨-((2 ^ j) ^ 2 * c), by ring⟩⟩

theorem hI_gI (hm : 1 ≤ m) (x : Torus (StrothTypeIndex.t201 m).k) : hI m (gI m x) = x := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [gI_vec, hI_vec, t201_vec_eq_iff]
  exact ⟨⟨-(4 * (2 ^ j) ^ 2 * a), by ring⟩, ⟨-((2 ^ j) ^ 2 * b), by ring⟩,
    ⟨-((2 ^ j) ^ 2 * c), by ring⟩⟩

theorem gI_U0 (hm : 1 ≤ m) (x : Torus (StrothTypeIndex.t201 m).k) :
    gI m (U0 m x) = (StrothTypeIndex.t201 m).action.φuv (gI m x) := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [U0_vec, gI_vec, gI_vec, t201_φuv_vec, t201_vec_eq_iff]
  exact ⟨⟨-(4 * a - 2 * b - c), by ring⟩,
    ⟨-(-3 * 2 ^ j * b + 2 ^ j * c - 4 * (2 ^ j) ^ 2 * b + 4 * (2 ^ j) ^ 2 * c + 2 * a - b - 2 * c),
      by ring⟩, ⟨-(2 ^ j * c + a - b), by ring⟩⟩

theorem gI_T0 (hm : 1 ≤ m) (x : Torus (StrothTypeIndex.t201 m).k) :
    gI m (T0 m x) = (StrothTypeIndex.t201 m).action.φt (gI m x) := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [T0_vec, gI_vec, gI_vec, t201_φt_vec, t201_vec_eq_iff]
  exact ⟨⟨-(4 * 2 ^ j * b - 4 * 2 ^ j * c + b + 2 * c), by ring⟩,
    ⟨-(2 ^ j * b - a + c), by ring⟩, ⟨-(2 ^ j * b - 2 ^ j * c + a), by ring⟩⟩

theorem gI_P0 (x : Torus (StrothTypeIndex.t201 m).k) :
    gI m (P0 m x) = (StrothTypeIndex.t201 m).action.φρ (gI m x) := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  rw [P0_vec, gI_vec, gI_vec, t201_φρ_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t201_rho_triv (hm : 1 ≤ m) (ruv rt : Torus (StrothTypeIndex.t201 m).k)
    (h1 : ruv + (StrothTypeIndex.t201 m).action.φuv ruv = 0)
    (h2 : rt + (StrothTypeIndex.t201 m).action.φt rt = 0)
    (h3 : ruv + (StrothTypeIndex.t201 m).action.φuv rt =
      rt + (StrothTypeIndex.t201 m).action.φt ruv) :
    ∃ d₀ : Torus (StrothTypeIndex.t201 m).k,
      (StrothTypeIndex.t201 m).action.φρ (ruv + (StrothTypeIndex.t201 m).action.φuv rt) =
          ruv - d₀ + (StrothTypeIndex.t201 m).action.φuv d₀ ∧
        (StrothTypeIndex.t201 m).action.φρ ruv =
          rt - d₀ + (StrothTypeIndex.t201 m).action.φt d₀ :=
  rho_triv_of_intertwine (gI_hI hm) (hI_gI hm) (gI_U0 hm) (gI_T0 hm) gI_P0 t200_rho_triv_on
    ruv rt h1 h2 h3


theorem zsmul_congr {y y' : ℤ} (h : (2 : ℤ) ^ (m + 2) ∣ y - y')
    (x : Torus (StrothTypeIndex.t201 m).k) : y • x = y' • x := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  rw [t201_zsmul_vec, t201_zsmul_vec, t201_vec_eq_iff]
  obtain ⟨k, hk⟩ := h
  refine ⟨⟨-(k * 4) * a, ?_⟩, ⟨-k * b, ?_⟩, ⟨-k * c, ?_⟩⟩
  · rw [pow_add] at hk; linear_combination (-a) * hk
  · linear_combination (-b) * hk
  · linear_combination (-c) * hk

theorem dvd_sub_of_zsmul_eq {y y' a c : ℤ}
    (h : y • Torus.ofInt (StrothTypeIndex.t201 m).k ![a, 1, c] = y' • Torus.ofInt _ ![a, 1, c]) :
    (2 : ℤ) ^ (m + 2) ∣ y - y' := by
  rw [t201_zsmul_vec, t201_zsmul_vec, t201_vec_eq_iff] at h
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h
  exact ⟨-k, by linear_combination -hk⟩

theorem c_eq_ofInt : (Torus.c : Torus (StrothTypeIndex.t201 m).k) = Torus.ofInt _ ![1, 0, 0] := by
  show gen _ 0 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem a_eq_ofInt : (Torus.a : Torus (StrothTypeIndex.t201 m).k) = Torus.ofInt _ ![0, 1, 0] := by
  show gen _ 1 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem b_eq_ofInt : (Torus.b : Torus (StrothTypeIndex.t201 m).k) = Torus.ofInt _ ![0, 0, 1] := by
  show gen _ 2 = _
  rw [Torus.ofInt_eq_zsmul_gens]
  simp

theorem φρ_c : (StrothTypeIndex.t201 m).action.φρ (Torus.c : Torus (StrothTypeIndex.t201 m).k) =
    Torus.c := by
  rw [c_eq_ofInt, t201_φρ_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φu_c : (StrothTypeIndex.t201 m).action.φu (Torus.c : Torus (StrothTypeIndex.t201 m).k) =
    Torus.c := by
  rw [c_eq_ofInt, t201_φu_vec]

theorem fix_ρ_c (x : Torus (StrothTypeIndex.t201 m).k)
    (h : (StrothTypeIndex.t201 m).action.φρ x = x) : ∃ l : ℤ, x = l • Torus.c := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  rw [t201_φρ_vec, t201_vec_eq_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  have hc : IsCoprime ((2 : ℤ) ^ (m + 2)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  obtain ⟨k3, hk3⟩ : (2 : ℤ) ^ (m + 2) ∣ c :=
    hc.dvd_of_dvd_mul_right ⟨k1 + k2, by linear_combination hk1 + hk2⟩
  refine ⟨a, ?_⟩
  rw [c_eq_ofInt, t201_zsmul_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨k3 - k1, by linear_combination -hk1 + hk3⟩,
    ⟨-k3, by linear_combination -hk3⟩⟩

theorem φuv_c_sub (l : ℤ) :
    (StrothTypeIndex.t201 m).action.φuv (l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) -
        l • Torus.ofInt _ ![1, 0, 0] = (-4 * l) • Torus.ofInt _ ![1, 1, 1] := by
  rw [t201_zsmul_vec, t201_φuv_vec, t201_sub_vec, t201_zsmul_vec, t201_vec_eq_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

theorem φt_c_sub (l : ℤ) :
    (StrothTypeIndex.t201 m).action.φt (l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0]) -
        l • Torus.ofInt _ ![1, 0, 0] = (-4 * l) • Torus.ofInt _ ![0, -1, 0] := by
  rw [t201_zsmul_vec, t201_φt_vec, t201_sub_vec, t201_zsmul_vec, t201_vec_eq_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

theorem cob_uv (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] -
        (StrothTypeIndex.t201 m).action.φuv (l • Torus.ofInt _ ![1, 0, 0]) =
      (4 * l) • Torus.ofInt _ ![1, 1, 1] := by
  rw [t201_zsmul_vec, t201_φuv_vec, t201_sub_vec, t201_zsmul_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem cob_t (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] -
        (StrothTypeIndex.t201 m).action.φt (l • Torus.ofInt _ ![1, 0, 0]) =
      (4 * l) • Torus.ofInt _ ![0, -1, 0] := by
  rw [t201_zsmul_vec, t201_φt_vec, t201_sub_vec, t201_zsmul_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem c_zsmul_eq_zero_iff (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] = 0 ↔ (2 : ℤ) ^ m ∣ l := by
  rw [t201_zsmul_vec, t201_vec_eq_zero_iff]
  simp

theorem c_zsmul_eq_iff (l l' : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] = l' • Torus.ofInt _ ![1, 0, 0] ↔
      (2 : ℤ) ^ m ∣ l - l' := by
  rw [t201_zsmul_vec, t201_zsmul_vec, t201_vec_eq_iff]
  simp only [mul_one, mul_zero, sub_zero, dvd_zero, and_true]
  exact dvd_sub_comm

theorem dvd_of_four_mul_zsmul_w {l : ℤ}
    (h : (4 * l) • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 1, 1] = 0) : (2 : ℤ) ^ m ∣ l := by
  rw [t201_zsmul_vec, t201_vec_eq_zero_iff] at h
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h
  exact ⟨k, mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) (by linear_combination hk)⟩

theorem φt_a : (StrothTypeIndex.t201 m).action.φt (Torus.ofInt _ ![0, 1, 0]) =
    (2 ^ (m + 1) - 1 : ℤ) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0] := by
  rw [t201_φt_vec, t201_zsmul_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φuv_a : (StrothTypeIndex.t201 m).action.φuv (Torus.ofInt _ ![0, 1, 0]) =
    (1 + 2 ^ (m + 1) : ℤ) • (StrothTypeIndex.t201 m).action.φρ
        (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]) -
      (StrothTypeIndex.t201 m).action.φρ ((StrothTypeIndex.t201 m).action.φρ
        (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0])) := by
  rw [t201_φuv_vec, t201_φρ_vec, t201_φρ_vec, t201_zsmul_vec, t201_sub_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem c_eq_a : Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 0, 0] =
    (StrothTypeIndex.t201 m).action.φuv (Torus.ofInt _ ![0, 1, 0]) - Torus.ofInt _ ![0, 1, 0] -
      (2 + 2 ^ (m + 1) : ℤ) • (StrothTypeIndex.t201 m).action.φρ (Torus.ofInt _ ![0, 1, 0]) := by
  rw [t201_φuv_vec, t201_φρ_vec, t201_zsmul_vec, t201_sub_vec, t201_sub_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φu_a : (StrothTypeIndex.t201 m).action.φu (Torus.ofInt _ ![0, 1, 0]) =
    (StrothTypeIndex.t201 m).action.φρ (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]) := by
  rw [t201_φu_vec, t201_φρ_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t201_comm_a (θ : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t201 m).action.φuv x) =
      (StrothTypeIndex.t201 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t201 m).action.φt x) = (StrothTypeIndex.t201 m).action.φt (θ x))
    (hρ : ∀ x, θ ((StrothTypeIndex.t201 m).action.φρ x) =
      (StrothTypeIndex.t201 m).action.φρ (θ x)) (hm : 1 ≤ m) :
    ∃ y s : ℤ, θ (Torus.ofInt _ ![0, 1, 0]) =
      Torus.ofInt (StrothTypeIndex.t201 m).k ![0, y, 2 ^ (m + 1) * s] := by
  obtain ⟨v0, v1, v2, hv⟩ := t201_exists_vec (θ (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]))
  have e1 : (StrothTypeIndex.t201 m).action.φt (θ (Torus.ofInt _ ![0, 1, 0])) =
      (2 ^ (m + 1) - 1 : ℤ) • θ (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]) := by
    rw [← ht, φt_a, map_zsmul]
  have e2 : (StrothTypeIndex.t201 m).action.φuv (θ (Torus.ofInt _ ![0, 1, 0])) =
      (1 + 2 ^ (m + 1) : ℤ) • (StrothTypeIndex.t201 m).action.φρ
          (θ (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0])) -
        (StrothTypeIndex.t201 m).action.φρ ((StrothTypeIndex.t201 m).action.φρ
          (θ (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0]))) := by
    rw [← huv, φuv_a, map_sub, map_zsmul, hρ, hρ, hρ]
  rw [hv, t201_φt_vec, t201_zsmul_vec, t201_vec_eq_iff] at e1
  rw [hv, t201_φuv_vec, t201_φρ_vec, t201_φρ_vec, t201_zsmul_vec, t201_sub_vec,
    t201_vec_eq_iff] at e2
  obtain ⟨⟨k0, hk0⟩, ⟨k1, hk1⟩, -⟩ := e1
  obtain ⟨-, ⟨k3, hk3⟩, -⟩ := e2
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  set α : ℤ := 2 * v0 - 2 ^ (j + 1) * v2 - k3 - k0 with hα
  have hv0 : v0 = 2 ^ (j + 1) * α := by
    have : 4 * v0 = 4 * (2 ^ (j + 1) * α) := by
      rw [hα]; linear_combination (-1 : ℤ) * hk3 - 4 * hk0
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) this
  have hv2' : (1 + 2 * 2 ^ j) * v2 = 4 * 2 ^ j * (k1 + α) := by
    have : 2 * ((1 + 2 * 2 ^ j) * v2) = 2 * (4 * 2 ^ j * (k1 + α)) := by
      linear_combination hk1 + 4 * hv0
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) this
  refine ⟨v1, k1 + α - 2 * 2 ^ j * (k1 + α) + 2 ^ j * v2, ?_⟩
  rw [hv, t201_vec_eq_iff]
  exact ⟨⟨-α, by linear_combination -hv0⟩, ⟨0, by ring⟩,
    ⟨0, by linear_combination (2 * 2 ^ j - 1) * hv2'⟩⟩

theorem t201_ext (θ θ' : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t201 m).action.φuv x) =
      (StrothTypeIndex.t201 m).action.φuv (θ x))
    (hρ : ∀ x, θ ((StrothTypeIndex.t201 m).action.φρ x) =
      (StrothTypeIndex.t201 m).action.φρ (θ x))
    (huv' : ∀ x, θ' ((StrothTypeIndex.t201 m).action.φuv x) =
      (StrothTypeIndex.t201 m).action.φuv (θ' x))
    (hρ' : ∀ x, θ' ((StrothTypeIndex.t201 m).action.φρ x) =
      (StrothTypeIndex.t201 m).action.φρ (θ' x))
    (ha : θ (Torus.ofInt _ ![0, 1, 0]) = θ' (Torus.ofInt _ ![0, 1, 0])) (x) : θ x = θ' x := by
  obtain ⟨x0, x1, x2, rfl⟩ := t201_exists_vec x
  have hx : Torus.ofInt (StrothTypeIndex.t201 m).k ![x0, x1, x2] =
      x0 • Torus.ofInt _ ![1, 0, 0] + x1 • Torus.ofInt _ ![0, 1, 0] +
        x2 • (StrothTypeIndex.t201 m).action.φρ (Torus.ofInt _ ![0, 1, 0]) := by
    rw [t201_φρ_vec, t201_zsmul_vec, t201_zsmul_vec, t201_zsmul_vec, t201_add_vec, t201_add_vec,
      t201_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  rw [hx, c_eq_a]
  simp only [map_add, map_sub, map_zsmul, huv, hρ, huv', hρ', ha]

theorem t201_scalar (hm : 1 ≤ m)
    (θ : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t201 m).action.φuv x) =
      (StrothTypeIndex.t201 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t201 m).action.φt x) = (StrothTypeIndex.t201 m).action.φt (θ x))
    (hu : ∀ x, θ ((StrothTypeIndex.t201 m).action.φu x) = (StrothTypeIndex.t201 m).action.φu (θ x))
    (hρ : ∀ x, θ ((StrothTypeIndex.t201 m).action.φρ x) =
      (StrothTypeIndex.t201 m).action.φρ (θ x)) :
    ∃ y : ℤ, ∀ x, θ x = y • x := by
  obtain ⟨y, s, hys⟩ := t201_comm_a θ huv ht hρ hm
  have e : (StrothTypeIndex.t201 m).action.φu (θ (Torus.ofInt _ ![0, 1, 0])) =
      (StrothTypeIndex.t201 m).action.φρ
        (θ (Torus.ofInt (StrothTypeIndex.t201 m).k ![0, 1, 0])) := by
    rw [← hu, ← hρ, φu_a]
  rw [hys, t201_φu_vec, t201_φρ_vec, t201_vec_eq_iff] at e
  obtain ⟨-, -, ⟨k, hk⟩⟩ := e
  refine ⟨y, t201_ext θ ((y : ℤ) • AddMonoidHom.id _) huv hρ (fun x => by
    rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
      AddMonoidHom.id_apply, map_zsmul]) (fun x => by
    rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
      AddMonoidHom.id_apply, map_zsmul]) ?_⟩
  rw [hys, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, t201_zsmul_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨k, by linear_combination hk⟩⟩

theorem φu_φρ (x : Torus (StrothTypeIndex.t201 m).k) :
    (StrothTypeIndex.t201 m).action.φu ((StrothTypeIndex.t201 m).action.φρ x) =
      (StrothTypeIndex.t201 m).action.φρ ((StrothTypeIndex.t201 m).action.φρ
        ((StrothTypeIndex.t201 m).action.φu x)) := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  rw [t201_φρ_vec, t201_φu_vec, t201_φu_vec, t201_φρ_vec, t201_φρ_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φu_φρφρ (x : Torus (StrothTypeIndex.t201 m).k) :
    (StrothTypeIndex.t201 m).action.φu ((StrothTypeIndex.t201 m).action.φρ
        ((StrothTypeIndex.t201 m).action.φρ x)) =
      (StrothTypeIndex.t201 m).action.φρ ((StrothTypeIndex.t201 m).action.φu x) := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec x
  rw [t201_φρ_vec, t201_φρ_vec, t201_φu_vec, t201_φu_vec, t201_φρ_vec, t201_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φu_φuv (x : Torus (StrothTypeIndex.t201 m).k) :
    (StrothTypeIndex.t201 m).action.φu ((StrothTypeIndex.t201 m).action.φuv x) =
      (StrothTypeIndex.t201 m).action.φuv ((StrothTypeIndex.t201 m).action.φu x) := by
  have h := DFunLike.congr_fun (StrothTypeIndex.t201 m).action.rels.uv_comm_u x
  simpa using h

theorem t201_uconj (hm : 1 ≤ m)
    (θ : Torus (StrothTypeIndex.t201 m).k →+ Torus (StrothTypeIndex.t201 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t201 m).action.φuv x) =
      (StrothTypeIndex.t201 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t201 m).action.φt x) = (StrothTypeIndex.t201 m).action.φt (θ x))
    (hρ : ∀ x, θ ((StrothTypeIndex.t201 m).action.φρ x) =
      (StrothTypeIndex.t201 m).action.φρ (θ x))
    (hinj : ∀ x, θ x = 0 → x = 0) :
    (∀ x, (StrothTypeIndex.t201 m).action.φu (θ ((StrothTypeIndex.t201 m).action.φu x)) = θ x) ∨
      ∀ x, (StrothTypeIndex.t201 m).action.φu (θ ((StrothTypeIndex.t201 m).action.φu x)) =
        (1 + 2 ^ (m + 1) : ℤ) • θ x := by
  obtain ⟨y, s, hys⟩ := t201_comm_a θ huv ht hρ hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hy : y % 2 = 1 := by
    by_contra hy0
    obtain ⟨y', rfl⟩ : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero (by omega)
    have h0 := hinj ((2 ^ (j + 1 + 1) : ℤ) • Torus.ofInt (StrothTypeIndex.t201 (j + 1)).k
      ![0, 1, 0]) (by
        rw [map_zsmul, hys, t201_zsmul_vec, t201_vec_eq_zero_iff]
        exact ⟨⟨0, by ring⟩, ⟨y', by ring⟩, ⟨2 ^ (j + 1) * s, by ring⟩⟩)
    rw [t201_zsmul_vec, t201_vec_eq_zero_iff] at h0
    exact Stroth34T200.not_two_pow_succ_dvd_mul_odd (j + 1 + 1) (z := 1) (by norm_num)
      (by simpa using h0.2.1)
  set ψ := ((StrothTypeIndex.t201 (j + 1)).action.φu).comp
    (θ.comp (StrothTypeIndex.t201 (j + 1)).action.φu) with hψ
  have hψuv : ∀ x, ψ ((StrothTypeIndex.t201 (j + 1)).action.φuv x) =
      (StrothTypeIndex.t201 (j + 1)).action.φuv (ψ x) := fun x => by
    simp only [hψ, AddMonoidHom.comp_apply]
    rw [φu_φuv, huv, φu_φuv]
  have hψρ : ∀ x, ψ ((StrothTypeIndex.t201 (j + 1)).action.φρ x) =
      (StrothTypeIndex.t201 (j + 1)).action.φρ (ψ x) := fun x => by
    simp only [hψ, AddMonoidHom.comp_apply]
    rw [φu_φρ, hρ, hρ, φu_φρφρ]
  have hψa : ψ (Torus.ofInt _ ![0, 1, 0]) = Torus.ofInt _ ![-(2 ^ (j + 1 + 1) * s),
      y - 2 ^ (j + 1 + 1) * s, -(2 ^ (j + 1 + 1) * s)] := by
    simp only [hψ, AddMonoidHom.comp_apply]
    rw [φu_a, hρ, hys, t201_φρ_vec, t201_φu_vec, t201_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  rcases Int.even_or_odd s with ⟨s', rfl⟩ | ⟨s', rfl⟩
  · left
    intro x
    refine t201_ext ψ θ hψuv hψρ huv hρ ?_ x
    rw [hψa, hys, t201_vec_eq_iff]
    exact ⟨⟨4 * s', by ring⟩, ⟨s', by ring⟩, ⟨2 * s', by ring⟩⟩
  · right
    intro x
    refine t201_ext ψ ((1 + 2 ^ (j + 1 + 1) : ℤ) • θ) hψuv hψρ
      (fun x => by rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, huv, map_zsmul])
      (fun x => by rw [AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, hρ, map_zsmul]) ?_ x
    obtain ⟨y', hy'⟩ : ∃ y', y = 2 * y' + 1 := ⟨y / 2, by omega⟩
    rw [hψa, AddMonoidHom.smul_apply, hys, t201_zsmul_vec, t201_vec_eq_iff]
    exact ⟨⟨2 * (2 * s' + 1) + 2 * (1 + 2 * 2 ^ (j + 1)) * (2 * s' + 1) * 0, by ring⟩,
      ⟨y' + 1 + s', by rw [hy']; ring⟩,
      ⟨(2 * s' + 1) * (1 + 2 ^ (j + 1)), by ring⟩⟩

theorem t201_normal_form (ruv rt : Torus (StrothTypeIndex.t201 m).k)
    (hu : (StrothTypeIndex.t201 m).action.φu ruv = ruv)
    (hρ1 : (StrothTypeIndex.t201 m).action.φρ (ruv + (StrothTypeIndex.t201 m).action.φuv rt) = ruv)
    (hρ2 : (StrothTypeIndex.t201 m).action.φρ ruv = rt) :
    ∃ p : ℤ, ruv = (2 * p) • Torus.ofInt (StrothTypeIndex.t201 m).k ![1, 1, 1] ∧
      rt = (2 * p) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, -1, 0] := by
  obtain ⟨x0, x1, x2, rfl⟩ := t201_exists_vec ruv
  subst hρ2
  rw [t201_φu_vec, t201_vec_eq_iff] at hu
  rw [t201_φρ_vec, t201_φuv_vec, t201_add_vec, t201_φρ_vec, t201_vec_eq_iff] at hρ1
  obtain ⟨-, ⟨k1, hk1⟩, -⟩ := hu
  obtain ⟨⟨k0, hk0⟩, -, ⟨k3, hk3⟩⟩ := hρ1
  set K : ℤ := 2 + 3 * 2 ^ (m + 1) + 2 ^ (m + 1) * 2 ^ (m + 1) with hK
  have hx2 : x2 = 2 * -(k3 + K * k1) := by
    have h2 : (2 : ℤ) ^ m * 2 ≠ 0 := by positivity
    have : 2 ^ m * 2 * x2 = 2 ^ m * 2 * (2 * -(k3 + K * k1)) := by
      rw [hK]; linear_combination (-1 : ℤ) * hk3 - (2 + 3 * 2 ^ (m + 1) +
        2 ^ (m + 1) * 2 ^ (m + 1)) * hk1
    exact mul_left_cancel₀ h2 this
  refine ⟨-(k3 + K * k1) + 2 ^ (m + 1) * k1, ?_, ?_⟩
  · rw [t201_zsmul_vec, t201_vec_eq_iff]
    exact ⟨⟨4 * k1 + 2 * x2 + k0, by linear_combination hk0 - hx2⟩,
      ⟨0, by linear_combination -hk1 - hx2⟩, ⟨k1, by linear_combination -hx2⟩⟩
  · rw [t201_φρ_vec, t201_zsmul_vec, t201_vec_eq_iff]
    exact ⟨⟨2 * x2 + k0, by linear_combination hk0⟩, ⟨-k1, by linear_combination hx2⟩,
      ⟨-k1, by linear_combination -hk1⟩⟩

theorem t201_fix_uv_exp (hm : 1 ≤ m) (d : Torus (StrothTypeIndex.t201 m).k)
    (h : (StrothTypeIndex.t201 m).action.φuv d = d) : (2 ^ (m + 1) : ℤ) • d = 0 := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec d
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [t201_φuv_vec, t201_vec_eq_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  rw [t201_zsmul_vec, t201_vec_eq_zero_iff]
  exact ⟨⟨2 * a, by ring⟩,
    ⟨a - 2 ^ j * b - 2 * 2 ^ j * k2, by linear_combination (-2 * 2 ^ j) * hk2⟩,
    ⟨a - 2 * 2 ^ j * k1 - 3 * 2 ^ j * c - 4 * 2 ^ j * 2 ^ j * c,
      by linear_combination (-2 * 2 ^ j) * hk1⟩⟩

theorem t201_fix_t_exp (hm : 1 ≤ m) (d : Torus (StrothTypeIndex.t201 m).k)
    (h : (StrothTypeIndex.t201 m).action.φt d = d) : (2 ^ (m + 1) : ℤ) • d = 0 := by
  obtain ⟨a, b, c, rfl⟩ := t201_exists_vec d
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [t201_φt_vec, t201_vec_eq_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  rw [t201_zsmul_vec, t201_vec_eq_zero_iff]
  exact ⟨⟨2 * a, by ring⟩,
    ⟨2 ^ j * b + a + 2 * 2 ^ j * k1 - 2 * 2 ^ j * k2,
      by linear_combination (2 * 2 ^ j) * hk1 - (2 * 2 ^ j) * hk2⟩,
    ⟨2 * 2 ^ j * k2 - 2 ^ j * c, by linear_combination (2 * 2 ^ j) * hk2⟩⟩

theorem t201_twist_fix_uv (hm : 1 ≤ m) {y : ℤ} (hy : y = -1 ∨ y = -1 + 2 ^ (m + 1)) :
    ∃ d : Torus (StrothTypeIndex.t201 m).k,
      y • (StrothTypeIndex.t201 m).action.φuv d = d ∧ (2 ^ (m + 1) : ℤ) • d ≠ 0 := by
  have hne : ∀ b c : ℤ, b % 2 = 1 →
      (2 ^ (m + 1) : ℤ) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, b, c] ≠ 0 := by
    intro b c hb h
    rw [t201_zsmul_vec, t201_vec_eq_zero_iff] at h
    exact Stroth34T200.not_two_pow_succ_dvd_mul_odd (m + 1) hb h.2.1
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rcases hy with rfl | rfl
  · refine ⟨Torus.ofInt _ ![0, 1, 2 ^ (j + 1) - 1], ?_, hne 1 _ (by norm_num)⟩
    rw [t201_φuv_vec, t201_zsmul_vec, t201_vec_eq_iff]
    exact ⟨⟨1, by ring⟩, ⟨-1 + 2 ^ j + 2 ^ (j + 1) * 2 ^ (j + 1), by ring⟩, ⟨1, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 1, 2 ^ (j + 1 + 1) - 1], ?_, hne 1 _ (by norm_num)⟩
    rw [t201_φuv_vec, t201_zsmul_vec, t201_vec_eq_iff]
    exact ⟨⟨2 - 4 * 2 ^ (j + 1), by ring⟩,
      ⟨3 * 2 ^ (j + 1) - 2 * 2 ^ (j + 1) * 2 ^ (j + 1) -
        4 * 2 ^ (j + 1) * 2 ^ (j + 1) * 2 ^ (j + 1), by ring⟩,
      ⟨1 - 2 * 2 ^ (j + 1), by ring⟩⟩

theorem t201_twist_fix_t (hm : 1 ≤ m) {y : ℤ} (hy : y = -1 ∨ y = -1 + 2 ^ (m + 1)) :
    ∃ d : Torus (StrothTypeIndex.t201 m).k,
      y • (StrothTypeIndex.t201 m).action.φt d = d ∧ (2 ^ (m + 1) : ℤ) • d ≠ 0 := by
  have hne : ∀ b c : ℤ, b % 2 = 1 →
      (2 ^ (m + 1) : ℤ) • Torus.ofInt (StrothTypeIndex.t201 m).k ![0, b, c] ≠ 0 := by
    intro b c hb h
    rw [t201_zsmul_vec, t201_vec_eq_zero_iff] at h
    exact Stroth34T200.not_two_pow_succ_dvd_mul_odd (m + 1) hb h.2.1
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rcases hy with rfl | rfl
  · refine ⟨Torus.ofInt _ ![0, 1, 2 ^ (j + 1)], ?_, hne 1 _ (by norm_num)⟩
    rw [t201_φt_vec, t201_zsmul_vec, t201_vec_eq_iff]
    exact ⟨⟨-(1 + 2 ^ (j + 1 + 1)), by ring⟩, ⟨-2 ^ j, by ring⟩, ⟨-2 ^ j, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 1, 0], ?_, hne 1 _ (by norm_num)⟩
    rw [t201_φt_vec, t201_zsmul_vec, t201_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨1 - 2 ^ (j + 1), by ring⟩, ⟨0, by ring⟩⟩

end Stroth34T201

end CFSG.CGT.Stroth77
