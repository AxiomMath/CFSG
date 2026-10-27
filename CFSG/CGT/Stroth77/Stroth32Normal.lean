module

public import CFSG.CGT.Stroth77.Stroth32Cent
public import CFSG.CGT.Stroth77.Stroth32H1

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth32H1

namespace Stroth32Normal

variable {m : ℕ}

theorem φρ_cab : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![1, 1, 1]) =
    -Torus.ofInt _ ![1, 1, 0] := by
  rw [t100_φρ_vec, t100_neg_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φρ_ca : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![1, 1, 0]) =
    Torus.ofInt _ ![1, 0, 1] := by
  rw [t100_φρ_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem φu_cab : (StrothTypeIndex.t100 m).action.φu (Torus.ofInt _ ![1, 1, 1]) =
    Torus.ofInt _ ![1, 1, 1] :=
  t100_φu_vec 1 1 1

theorem ofInt_eq_eigen (a b c : ℤ) :
    Torus.ofInt (StrothTypeIndex.t100 m).k ![a, b, c] =
      (b + c - a) • Torus.ofInt _ ![1, 1, 1] + (a - c) • Torus.ofInt _ ![1, 1, 0] +
        (a - b) • Torus.ofInt _ ![1, 0, 1] := by
  rw [t100_zsmul_vec, t100_zsmul_vec, t100_zsmul_vec, t100_add_vec, t100_add_vec,
    t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem ext_eigen (φ ψ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (h₁ : φ (Torus.ofInt _ ![1, 1, 1]) = ψ (Torus.ofInt _ ![1, 1, 1]))
    (h₂ : φ (Torus.ofInt _ ![1, 1, 0]) = ψ (Torus.ofInt _ ![1, 1, 0]))
    (h₃ : φ (Torus.ofInt _ ![1, 0, 1]) = ψ (Torus.ofInt _ ![1, 0, 1]))
    (x : Torus (StrothTypeIndex.t100 m).k) : φ x = ψ x := by
  obtain ⟨a, b, c, rfl⟩ := t100_exists_vec x
  rw [ofInt_eq_eigen]
  simp only [map_add, map_zsmul, h₁, h₂, h₃]

theorem t100_scalar
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t100 m).action.φuv x) =
      (StrothTypeIndex.t100 m).action.φuv (θ x))
    (hu : ∀ x, θ ((StrothTypeIndex.t100 m).action.φu x) =
      (StrothTypeIndex.t100 m).action.φu (θ x))
    (hρ : ∀ x, θ ((StrothTypeIndex.t100 m).action.φρ x) =
      (StrothTypeIndex.t100 m).action.φρ (θ x)) :
    ∃ y : ℤ, ∀ x, θ x = y • x := by
  obtain ⟨α, s, r, h⟩ := Stroth32Cent.eq_of_twist₁ (y := θ (Torus.ofInt _ ![1, 1, 1]))
    (by rw [← huv, Stroth32Cent.φuv_cab])
  have hu₁ := hu (Torus.ofInt _ ![1, 1, 1])
  rw [φu_cab, h, t100_φu_vec, t100_vec_eq_iff] at hu₁
  obtain ⟨-, ⟨w, hw⟩, -⟩ := hu₁
  have h₁ : θ (Torus.ofInt _ ![1, 1, 1]) = (α + 2 ^ m * s) • Torus.ofInt _ ![1, 1, 1] := by
    rw [h, t100_zsmul_vec, t100_vec_eq_iff]
    exact ⟨⟨s, by ring⟩, ⟨0, by ring⟩, ⟨-w, by linear_combination -hw⟩⟩
  have h₂ : θ (Torus.ofInt _ ![1, 1, 0]) = (α + 2 ^ m * s) • Torus.ofInt _ ![1, 1, 0] := by
    have := hρ (Torus.ofInt _ ![1, 1, 1])
    rw [φρ_cab, map_neg, h₁, map_zsmul, φρ_cab, smul_neg] at this
    exact neg_injective this
  have h₃ : θ (Torus.ofInt _ ![1, 0, 1]) = (α + 2 ^ m * s) • Torus.ofInt _ ![1, 0, 1] := by
    rw [← φρ_ca, hρ, h₂, map_zsmul]
  refine ⟨α + 2 ^ m * s, fun x => ?_⟩
  have key := ext_eigen θ ((α + 2 ^ m * s) • AddMonoidHom.id _)
    (by rw [AddMonoidHom.smul_apply, AddMonoidHom.id_apply]; exact h₁)
    (by rw [AddMonoidHom.smul_apply, AddMonoidHom.id_apply]; exact h₂)
    (by rw [AddMonoidHom.smul_apply, AddMonoidHom.id_apply]; exact h₃) x
  rwa [AddMonoidHom.smul_apply, AddMonoidHom.id_apply] at key

theorem t100_zsmul_congr {y y' : ℤ} (h : (2 : ℤ) ^ (m + 1) ∣ y - y')
    (x : Torus (StrothTypeIndex.t100 m).k) : y • x = y' • x := by
  obtain ⟨a, b, c, rfl⟩ := t100_exists_vec x
  rw [t100_zsmul_vec, t100_zsmul_vec, t100_vec_eq_iff]
  obtain ⟨k, hk⟩ := h
  exact ⟨⟨-(k * 2) * a, by linear_combination (-a) * hk⟩, ⟨-k * b, by linear_combination (-b) * hk⟩,
    ⟨-k * c, by linear_combination (-c) * hk⟩⟩

theorem t100_dvd_sub_of_zsmul_eq {y y' a c : ℤ}
    (h : y • Torus.ofInt (StrothTypeIndex.t100 m).k ![a, 1, c] = y' • Torus.ofInt _ ![a, 1, c]) :
    (2 : ℤ) ^ (m + 1) ∣ y - y' := by
  rw [t100_zsmul_vec, t100_zsmul_vec, t100_vec_eq_iff] at h
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h
  exact ⟨-k, by linear_combination -hk⟩

theorem t100_φρ_c :
    (StrothTypeIndex.t100 m).action.φρ (Torus.c : Torus (StrothTypeIndex.t100 m).k) = Torus.c := by
  rw [t100_c_eq_ofInt, t100_φρ_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t100_φu_c :
    (StrothTypeIndex.t100 m).action.φu (Torus.c : Torus (StrothTypeIndex.t100 m).k) = Torus.c := by
  rw [t100_c_eq_ofInt, t100_φu_vec]

theorem t100_fix_ρ_c (x : Torus (StrothTypeIndex.t100 m).k)
    (h : (StrothTypeIndex.t100 m).action.φρ x = x) : ∃ l : ℤ, x = l • Torus.c := by
  obtain ⟨a, b, c, rfl⟩ := t100_exists_vec x
  rw [t100_φρ_vec, t100_vec_eq_iff] at h
  obtain ⟨-, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := h
  have hc : IsCoprime ((2 : ℤ) ^ (m + 1)) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  obtain ⟨k3, hk3⟩ : (2 : ℤ) ^ (m + 1) ∣ c :=
    hc.dvd_of_dvd_mul_right ⟨k1 + k2, by linear_combination hk1 + hk2⟩
  refine ⟨a, ?_⟩
  rw [t100_c_eq_ofInt, t100_zsmul_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨k3 - k1, by linear_combination -hk1 + hk3⟩,
    ⟨-k3, by linear_combination -hk3⟩⟩

theorem t100_φuv_c_sub (l : ℤ) :
    (StrothTypeIndex.t100 m).action.φuv (l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) -
        l • Torus.ofInt _ ![1, 0, 0] = (-2 * l) • Torus.ofInt _ ![2, 1, 1] := by
  rw [t100_zsmul_vec, t100_φuv_vec, t100_sub_vec, t100_zsmul_vec, t100_vec_eq_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

theorem t100_φt_c_sub (l : ℤ) :
    (StrothTypeIndex.t100 m).action.φt (l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) -
        l • Torus.ofInt _ ![1, 0, 0] = (-2 * l) • Torus.ofInt _ ![0, -1, 0] := by
  rw [t100_zsmul_vec, t100_φt_vec, t100_sub_vec, t100_zsmul_vec, t100_vec_eq_iff]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> ring

theorem t100_cob_uv (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] -
        (StrothTypeIndex.t100 m).action.φuv (l • Torus.ofInt _ ![1, 0, 0]) =
      (2 * l) • Torus.ofInt _ ![2, 1, 1] := by
  rw [t100_zsmul_vec, t100_φuv_vec, t100_sub_vec, t100_zsmul_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t100_cob_t (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] -
        (StrothTypeIndex.t100 m).action.φt (l • Torus.ofInt _ ![1, 0, 0]) =
      (2 * l) • Torus.ofInt _ ![0, -1, 0] := by
  rw [t100_zsmul_vec, t100_φt_vec, t100_sub_vec, t100_zsmul_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

theorem t100_c_zsmul_eq_zero_iff (l : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] = 0 ↔ (2 : ℤ) ^ m ∣ l := by
  rw [t100_zsmul_vec, t100_vec_eq_zero_iff]
  simp

theorem t100_c_zsmul_eq_iff (l l' : ℤ) :
    l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] = l' • Torus.ofInt _ ![1, 0, 0] ↔
      (2 : ℤ) ^ m ∣ l - l' := by
  rw [t100_zsmul_vec, t100_zsmul_vec, t100_vec_eq_iff]
  simp only [mul_one, mul_zero, sub_zero, dvd_zero, and_true]
  exact dvd_sub_comm

theorem t100_dvd_of_two_mul_zsmul_w {l : ℤ}
    (h : (2 * l) • Torus.ofInt (StrothTypeIndex.t100 m).k ![2, 1, 1] = 0) : (2 : ℤ) ^ m ∣ l := by
  rw [t100_zsmul_vec, t100_vec_eq_zero_iff] at h
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h
  exact ⟨k, mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) (by linear_combination hk)⟩

theorem t100_normal_form (ruv rt : Torus (StrothTypeIndex.t100 m).k)
    (hu : (StrothTypeIndex.t100 m).action.φu ruv = ruv)
    (hρ1 : (StrothTypeIndex.t100 m).action.φρ (ruv + (StrothTypeIndex.t100 m).action.φuv rt) = ruv)
    (hρ2 : (StrothTypeIndex.t100 m).action.φρ ruv = rt) :
    ∃ p : ℤ, ruv = p • Torus.ofInt (StrothTypeIndex.t100 m).k ![2, 1, 1] ∧
      rt = p • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, -1, 0] := by
  obtain ⟨x0, x1, x2, rfl⟩ := t100_exists_vec ruv
  subst hρ2
  rw [t100_φu_vec, t100_vec_eq_iff] at hu
  rw [t100_φρ_vec, t100_φuv_vec, t100_add_vec, t100_φρ_vec, t100_vec_eq_iff] at hρ1
  obtain ⟨-, ⟨k1, hk1⟩, -⟩ := hu
  obtain ⟨⟨k0, hk0⟩, -, -⟩ := hρ1
  refine ⟨x1, ?_, ?_⟩
  · rw [t100_zsmul_vec, t100_vec_eq_iff]
    exact ⟨⟨4 * k1 + k0, by linear_combination 2 * hk1 + hk0⟩, ⟨0, by ring⟩,
      ⟨k1, by linear_combination hk1⟩⟩
  · rw [t100_φρ_vec, t100_zsmul_vec, t100_vec_eq_iff]
    exact ⟨⟨k0, by linear_combination hk0⟩, ⟨-k1, by linear_combination -hk1⟩,
      ⟨-k1, by linear_combination -hk1⟩⟩

theorem t100_sq_cases (hm : 1 ≤ m) {y : ℤ} (h : (2 : ℤ) ^ (m + 1) ∣ y * y - 1)
    (h1 : ¬ (2 : ℤ) ^ (m + 1) ∣ y - 1) :
    (2 : ℤ) ^ (m + 1) ∣ y - (1 + 2 ^ m) ∨ (2 : ℤ) ^ (m + 1) ∣ y + 1 ∨
      (2 : ℤ) ^ (m + 1) ∣ y - (-1 + 2 ^ m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, hk⟩ := h
  have hodd : Odd y := by
    rcases Int.even_or_odd y with ⟨r, rfl⟩ | hy
    · have h2 : (2 : ℤ) ∣ 1 := ⟨2 * r * r - 2 * 2 ^ n * k, by linear_combination -hk⟩
      exact absurd h2 (by norm_num)
    · exact hy
  obtain ⟨a, rfl⟩ := hodd
  have hdiv : (2 : ℤ) ^ n ∣ a * (a + 1) :=
    ⟨k, mul_left_cancel₀ (four_ne_zero : (4 : ℤ) ≠ 0) (by linear_combination hk)⟩
  have key : (2 : ℤ) ^ n ∣ a ∨ (2 : ℤ) ^ n ∣ a + 1 := by
    rcases Int.even_or_odd a with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact Or.inl (((show IsCoprime (2 : ℤ) (a + 1) from
        ⟨-r, 1, by rw [hr]; ring⟩).pow_left).dvd_of_dvd_mul_right hdiv)
    · exact Or.inr (((show IsCoprime (2 : ℤ) a from
        ⟨-r, 1, by rw [hr]; ring⟩).pow_left).dvd_of_dvd_mul_left hdiv)
  rcases key with ⟨j, hj⟩ | ⟨j, hj⟩
  · rcases Int.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact absurd ⟨i, by linear_combination 2 * hj⟩ h1
    · exact Or.inl ⟨i, by linear_combination 2 * hj⟩
  · rcases Int.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨i, by linear_combination 2 * hj⟩)
    · exact Or.inr (Or.inr ⟨i, by linear_combination 2 * hj⟩)

end Stroth32Normal

open Stroth32Normal

namespace StrothWeakTypeData

variable {G : Type} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m))

theorem t100_c_pow_eq (j : ℕ) :
    (dD.c : G) ^ j = dD.ofT ((j : ℤ) • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) := by
  rw [dD.ofT_zsmul, zpow_natCast, ← t100_c_eq]

theorem t100_c_inv_eq :
    (dD.c : G)⁻¹ = dD.ofT ((-1 : ℤ) • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) := by
  rw [dD.ofT_zsmul, zpow_neg_one, ← t100_c_eq]

theorem t100_c_inv_mul_pow_eq (j : ℕ) :
    (dD.c : G)⁻¹ * (dD.c : G) ^ j =
      dD.ofT ((-1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t100_c_eq, zpow_natCast, zpow_neg_one]

theorem t100_a_inv_eq :
    (dD.a : G)⁻¹ = dD.ofT ((-1 : ℤ) • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0]) := by
  rw [dD.ofT_zsmul, zpow_neg_one, ← t100_a_eq]

theorem t100_a_mul_pow_eq (j : ℕ) :
    (dD.a : G) * (dD.a : G) ^ j =
      dD.ofT ((1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0]) := by
  rw [add_zsmul, dD.ofT_add, one_zsmul, dD.ofT_zsmul, ← t100_a_eq, zpow_natCast]

theorem t100_a_inv_mul_pow_eq (j : ℕ) :
    (dD.a : G)⁻¹ * (dD.a : G) ^ j =
      dD.ofT ((-1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t100_a_eq, zpow_natCast, zpow_neg_one]

theorem t100_b_inv_eq :
    (dD.b : G)⁻¹ = dD.ofT ((-1 : ℤ) • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 1]) := by
  rw [dD.ofT_zsmul, zpow_neg_one, ← t100_b_eq]

theorem t100_b_mul_pow_eq (j : ℕ) :
    (dD.b : G) * (dD.b : G) ^ j =
      dD.ofT ((1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 1]) := by
  rw [add_zsmul, dD.ofT_add, one_zsmul, dD.ofT_zsmul, ← t100_b_eq, zpow_natCast]

theorem t100_b_inv_mul_pow_eq (j : ℕ) :
    (dD.b : G)⁻¹ * (dD.b : G) ^ j =
      dD.ofT ((-1 + (j : ℤ)) • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 1]) := by
  rw [add_zsmul, dD.ofT_add, dD.ofT_zsmul, dD.ofT_zsmul, ← t100_b_eq, zpow_natCast, zpow_neg_one]

theorem t100_c_sq_mul_a_mul_b_eq :
    (dD.c : G) ^ 2 * dD.a * dD.b = dD.ofT (Torus.ofInt (StrothTypeIndex.t100 m).k ![2, 1, 1]) := by
  have h : Torus.ofInt (StrothTypeIndex.t100 m).k ![2, 1, 1] =
      ((2 : ℕ) : ℤ) • Torus.ofInt _ ![1, 0, 0] + Torus.ofInt _ ![0, 1, 0] +
        Torus.ofInt _ ![0, 0, 1] := by
    rw [t100_zsmul_vec, t100_add_vec, t100_add_vec]; norm_num
  rw [h, dD.ofT_add, dD.ofT_add, dD.ofT_zsmul, zpow_natCast, ← t100_c_eq, ← t100_a_eq,
    ← t100_b_eq]

theorem t100_a_inv_eq_ofT :
    (dD.a : G)⁻¹ = dD.ofT (Torus.ofInt (StrothTypeIndex.t100 m).k ![0, -1, 0]) := by
  have h : Torus.ofInt (StrothTypeIndex.t100 m).k ![0, -1, 0] =
      (-1 : ℤ) • Torus.ofInt _ ![0, 1, 0] := by
    rw [t100_zsmul_vec]; norm_num
  rw [h, ← t100_a_inv_eq]

end StrothWeakTypeData

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)}

theorem t100_D_le_R1 (hS : Local.Setting (F.S : Subgroup G) D) : D ≤ hS.R1 dD.uv dD.t :=
  fun _ hd =>
    ⟨hS.D_le_R hd, (dD.crdT_cocycle_of_mem_uv hd).1, (dD.crdT_cocycle_of_mem_t hd).1⟩

theorem t100_crdT_eq_of_proj_eq (hS : Local.Setting (F.S : Subgroup G) D) {d : G} (hd : d ∈ D)
    (hp : hS.proj dD.ρ d = d) :
    ∃ l : ℤ, crdT dD.e d = l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] := by
  have hρd : dD.ρ⁻¹ * d * dD.ρ ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hd
  have h1 := hS.proj_eq_of_mem (hS.D_le_R hρd)
  rw [hp] at h1
  obtain ⟨l, hl⟩ := t100_fix_ρ_c (crdT dD.e d) (by
    rw [← crdT_conj dD.e dD.ρ_mem dD.ρ_conj hd, ← h1])
  exact ⟨l, by rw [hl, t100_c_eq_ofInt]⟩

end StrothFrame.IsD

structure Normal100 {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    (hS : Local.Setting (F.S : Subgroup G) D) (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m))
    (e : G) (y p : ℤ) : Prop where
  mem : e ∈ hS.R1 dD.uv dD.t
  proj : hS.proj dD.ρ e = e
  comm : dD.u * e = e * dD.u
  scalar : ∀ v, dD.thetaT (hS.R_le_normalizer mem.1) v = y • v
  ruv : crdT dD.e (e⁻¹ * dD.uv * e * dD.uv⁻¹) =
    p • Torus.ofInt (StrothTypeIndex.t100 m).k ![2, 1, 1]
  rt : crdT dD.e (e⁻¹ * dD.t * e * dD.t⁻¹) = p • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, -1, 0]

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)}

theorem exists_normal100 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) (hpg : hS.proj dD.ρ g * g⁻¹ ∈ D) :
    ∃ d ∈ D, ∃ y p : ℤ, Normal100 hS dD (g * d) y p := by
  obtain ⟨d, hd, hp, hu⟩ := h.exists_normalized hS t100_fix_ρ_c t100_φu_c hm hfus hg.1 hpg
    (h.t100_conj_u_mul_inv_mem hS hm hg hpg)
  have hmem : g * d ∈ hS.R1 dD.uv dD.t := mul_mem hg (t100_D_le_R1 hS hd)
  have heN := hS.R_le_normalizer hmem.1
  obtain ⟨y, hy⟩ := t100_scalar (dD.thetaT heN)
    (fun x => by
      have := dD.thetaT_comm_of_conj_mem heN dD.uv_mem hmem.2.1 x
      rwa [dD.thetaT_uv, dD.thetaT_uv] at this)
    (fun x => thetaT_comm_u hS hmem.1 (by
      rw [show dD.u⁻¹ * (g * d) * dD.u = dD.u⁻¹ * (dD.u * (g * d)) by rw [hu]; group]
      simp) x)
    (fun x => thetaT_comm_rho hS hmem.1 (by rw [hp, mul_inv_cancel]; exact one_mem D) x)
  obtain ⟨n1, n2, n3, -⟩ := h.cocycle_normalized hS hmem hp hu
  obtain ⟨p, hp1, hp2⟩ := t100_normal_form _ _ n3 n1 n2
  exact ⟨d, hd, y, p, hmem, hp, hu, hy, hp1, hp2⟩

theorem normal100_one (hS : Local.Setting (F.S : Subgroup G) D) : Normal100 hS dD 1 1 0 where
  mem := one_mem _
  proj := proj_rho_one hS
  comm := by rw [mul_one, one_mul]
  scalar v := by rw [one_zsmul]; exact dD.thetaT_of_mem _ (one_mem D) v
  ruv := by rw [zero_zsmul, show (1 : G)⁻¹ * dD.uv * 1 * dD.uv⁻¹ = 1 by group, crdT_one]
  rt := by rw [zero_zsmul, show (1 : G)⁻¹ * dD.t * 1 * dD.t⁻¹ = 1 by group, crdT_one]

end StrothFrame.IsD

namespace Normal100

open StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)} {hS : Local.Setting (F.S : Subgroup G) D}

theorem mul_c {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) (μ : ℤ) :
    Normal100 hS dD (e * dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]))
      y (p - 2 * μ) := by
  set d := dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) with hd_def
  have hd : d ∈ D := dD.ofT_mem _
  have hdN : d ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hd
  have hcd : crdT dD.e d = μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] :=
    dD.crdT_ofT _
  have heN := hS.R_le_normalizer hn.mem.1
  have hρd : dD.ρ⁻¹ * d * dD.ρ = d := by
    refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp hd) hd ?_
    rw [crdT_conj dD.e dD.ρ_mem dD.ρ_conj hd, hcd, map_zsmul, ← t100_c_eq_ofInt, t100_φρ_c]
  have hud : dD.u * d = d * dD.u := by
    have h1 : dD.u⁻¹ * d * dD.u = d := by
      refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp dD.u_mem _).mp hd) hd ?_
      rw [crdT_conj dD.e dD.u_mem dD.u_conj hd, hcd, map_zsmul, ← t100_c_eq_ofInt, t100_φu_c]
    calc dD.u * d = dD.u * (dD.u⁻¹ * d * dD.u) := by rw [h1]
      _ = d * dD.u := by group
  have huv := dD.crdT_cocycle_mul hdN hn.mem.2.1 (dD.crdT_cocycle_of_mem_uv hd).1
  have ht := dD.crdT_cocycle_mul hdN hn.mem.2.2 (dD.crdT_cocycle_of_mem_t hd).1
  refine ⟨mul_mem hn.mem (t100_D_le_R1 hS hd), ?_, ?_, fun v => ?_, ?_, ?_⟩
  · rw [hS.proj_mul dD.ρ_mem hn.mem.1 (hS.D_le_R hd), hn.proj,
      hS.proj_eq_of_mem (by rw [hρd]; exact hS.D_le_R hd), hρd]
  · rw [← mul_assoc, hn.comm, mul_assoc, hud, ← mul_assoc]
  · rw [dD.thetaT_congr _ (mul_mem heN hdN) rfl, dD.thetaT_mul heN hdN, dD.thetaT_of_mem hdN hd,
      hn.scalar]
  · rw [huv.2, dD.thetaT_of_mem hdN hd, hn.ruv, (dD.crdT_cocycle_of_mem_uv hd).2, hcd,
      t100_φuv_c_sub, ← add_zsmul]
    congr 1; ring
  · rw [ht.2, dD.thetaT_of_mem hdN hd, hn.rt, (dD.crdT_cocycle_of_mem_t hd).2, hcd, t100_φt_c_sub,
      ← add_zsmul]
    congr 1; ring

theorem mul {e f : G} {y p y' p' : ℤ} (he : Normal100 hS dD e y p)
    (hf : Normal100 hS dD f y' p') : Normal100 hS dD (e * f) (y * y') (y' * p + p') := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  refine ⟨mul_mem he.mem hf.mem, ?_, ?_, fun v => ?_, ?_, ?_⟩
  · rw [hS.proj_mul dD.ρ_mem he.mem.1 hf.mem.1, he.proj, hf.proj]
  · rw [← mul_assoc, he.comm, mul_assoc, hf.comm, mul_assoc]
  · rw [dD.thetaT_congr _ (mul_mem heN hfN) rfl, dD.thetaT_mul heN hfN, he.scalar, map_zsmul,
      hf.scalar, smul_smul]
  · rw [(dD.crdT_cocycle_mul hfN he.mem.2.1 hf.mem.2.1).2, he.ruv, map_zsmul, hf.scalar,
      smul_smul, hf.ruv, ← add_zsmul, mul_comm y' p]
  · rw [(dD.crdT_cocycle_mul hfN he.mem.2.2 hf.mem.2.2).2, he.rt, map_zsmul, hf.scalar,
      smul_smul, hf.rt, ← add_zsmul, mul_comm y' p]

theorem mem_of_two_dvd (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p)
    (hp : (2 : ℤ) ∣ p) : e ∈ D := by
  obtain ⟨μ, rfl⟩ := hp
  exact h.mem_of_cocycle_cob hS hn.mem.1 hn.mem.2.1 hn.mem.2.2
    (μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) (by rw [hn.ruv, t100_cob_uv])
    (by rw [hn.rt, t100_cob_t])

theorem mul_inv_mem (h : F.IsD D dD) {e f : G} {y p y' p' : ℤ} (he : Normal100 hS dD e y p)
    (hf : Normal100 hS dD f y' p') (hp : (2 : ℤ) ∣ p - p') : e * f⁻¹ ∈ D := by
  obtain ⟨μ, hμ⟩ := hp
  refine h.mul_inv_mem_of_cocycle_cob hS he.mem hf.mem
    (μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) ?_ ?_
  · rw [he.ruv, hf.ruv, t100_cob_uv, ← add_zsmul]
    congr 1; linear_combination hμ
  · rw [he.rt, hf.rt, t100_cob_t, ← add_zsmul]
    congr 1; linear_combination hμ

theorem scalar_dvd {e f : G} {y p y' p' : ℤ} (he : Normal100 hS dD e y p)
    (hf : Normal100 hS dD f y' p') (hef : e * f⁻¹ ∈ D) : (2 : ℤ) ^ (m + 1) ∣ y - y' := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  have hdN : e * f⁻¹ ∈ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer hef
  refine t100_dvd_sub_of_zsmul_eq (a := 0) (c := 0) ?_
  rw [← he.scalar, ← hf.scalar, dD.thetaT_congr heN (mul_mem hdN hfN) (by group),
    dD.thetaT_mul hdN hfN, dD.thetaT_of_mem hdN hef]

theorem mul_inv_mem_of_scalar {e f : G} {y p y' p' : ℤ} (he : Normal100 hS dD e y p)
    (hf : Normal100 hS dD f y' p') (hy : (2 : ℤ) ^ (m + 1) ∣ y - y') : e * f⁻¹ ∈ D := by
  have heN := hS.R_le_normalizer he.mem.1
  have hfN := hS.R_le_normalizer hf.mem.1
  refine dD.mem_of_thetaT_id hS (mul_mem (hS.R_le_S he.mem.1) (inv_mem (hS.R_le_S hf.mem.1)))
    (mul_mem heN (inv_mem hfN)) fun v => ?_
  rw [dD.thetaT_mul heN (inv_mem hfN), he.scalar, t100_zsmul_congr hy, ← hf.scalar,
    dD.thetaT_inv_thetaT]

theorem scalar_dvd_of_mem {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) (he : e ∈ D) :
    (2 : ℤ) ^ (m + 1) ∣ y - 1 :=
  hn.scalar_dvd (normal100_one hS) (by simpa using he)

theorem mem_of_scalar {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p)
    (hy : (2 : ℤ) ^ (m + 1) ∣ y - 1) : e ∈ D := by
  simpa using hn.mul_inv_mem_of_scalar (normal100_one hS) hy

theorem eq (h : F.IsD D dD) {e f : G} {y p y' p' : ℤ} (he : Normal100 hS dD e y p)
    (hf : Normal100 hS dD f y' p') (hp : (2 : ℤ) ^ (m + 1) ∣ p - p') : e = f := by
  have hef : e * f⁻¹ ∈ D := he.mul_inv_mem h hf (dvd_trans ⟨2 ^ m, by ring⟩ hp)
  have hfN := hS.R_le_normalizer hf.mem.1
  have hpr : hS.proj dD.ρ (e * f⁻¹) = e * f⁻¹ := by
    rw [hS.proj_mul dD.ρ_mem he.mem.1 (inv_mem hf.mem.1), he.proj, proj_rho_inv hS hf.mem.1,
      hf.proj]
  obtain ⟨l, hl⟩ := t100_crdT_eq_of_proj_eq hS hef hpr
  have key := (dD.crdT_cocycle_mul hfN (dD.crdT_cocycle_of_mem_uv hef).1 hf.mem.2.1).2
  rw [show e * f⁻¹ * f = e by group, he.ruv, hf.ruv, t100_zsmul_congr hp] at key
  have k0 : dD.thetaT hfN (crdT dD.e ((e * f⁻¹)⁻¹ * dD.uv * (e * f⁻¹) * dD.uv⁻¹)) = 0 :=
    (add_left_inj _).mp (by rw [zero_add]; exact key.symm)
  have h0 : crdT dD.e ((e * f⁻¹)⁻¹ * dD.uv * (e * f⁻¹) * dD.uv⁻¹) = 0 := by
    have := congrArg (dD.thetaT (inv_mem hfN)) k0
    rwa [dD.thetaT_inv_thetaT, map_zero] at this
  rw [(dD.crdT_cocycle_of_mem_uv hef).2, hl, t100_φuv_c_sub] at h0
  have hl0 : l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0] = 0 := by
    rw [t100_c_zsmul_eq_zero_iff]
    exact dvd_neg.mp (t100_dvd_of_two_mul_zsmul_w
      (by rw [show (2 * -l : ℤ) = -2 * l by ring]; exact h0))
  have h1 : e * f⁻¹ = 1 := crdT_inj dD.e hef (one_mem D) (by rw [hl, hl0, crdT_one])
  exact mul_inv_eq_one.mp h1

theorem eq_ofT (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) {μ : ℤ}
    (hμ : (2 : ℤ) ^ (m + 1) ∣ p + 2 * μ) :
    e = dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) := by
  have h1 := (normal100_one hS (dD := dD)).mul_c μ
  rw [one_mul] at h1
  exact hn.eq h h1 (by rw [zero_sub, sub_neg_eq_add]; exact hμ)

theorem renorm {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) {p' : ℤ} (h : (2 : ℤ) ∣ p - p') :
    ∃ d ∈ D, Normal100 hS dD (e * d) y p' := by
  obtain ⟨μ, hμ⟩ := h
  refine ⟨_, dD.ofT_mem (μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]), ?_⟩
  have := hn.mul_c μ
  rwa [show p - 2 * μ = p' by linear_combination hμ] at this

theorem c_conj_eq {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ m ∣ y - l) :
    e⁻¹ * (dD.c : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have hc : (dD.c : G) ∈ D := (dD.c).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp hc) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN hc, dD.crdT_ofT, dD.t100_c_eq, dD.crdT_ofT, hn.scalar,
    (t100_c_zsmul_eq_iff y l).mpr hy]

theorem a_conj_eq {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ (m + 1) ∣ y - l) :
    e⁻¹ * (dD.a : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 1, 0]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have ha : (dD.a : G) ∈ D := (dD.a).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp ha) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN ha, dD.crdT_ofT, dD.t100_a_eq, dD.crdT_ofT, hn.scalar,
    t100_zsmul_congr hy]

theorem b_conj_eq {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) {l : ℤ}
    (hy : (2 : ℤ) ^ (m + 1) ∣ y - l) :
    e⁻¹ * (dD.b : G) * e = dD.ofT (l • Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 0, 1]) := by
  have heN := hS.R_le_normalizer hn.mem.1
  have hb : (dD.b : G) ∈ D := (dD.b).2
  refine crdT_inj dD.e ((Subgroup.mem_normalizer_iff''.mp heN _).mp hb) (dD.ofT_mem _) ?_
  rw [← dD.thetaT_crdT heN hb, dD.crdT_ofT, dD.t100_b_eq, dD.crdT_ofT, hn.scalar,
    t100_zsmul_congr hy]

theorem uv_conj_eq {e : G} {y : ℤ} (hn : Normal100 hS dD e y 1) :
    e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv := by
  have key : e⁻¹ * dD.uv * e * dD.uv⁻¹ = (dD.c : G) ^ 2 * dD.a * dD.b := by
    rw [dD.t100_c_sq_mul_a_mul_b_eq]
    exact crdT_inj dD.e hn.mem.2.1 (dD.ofT_mem _) (by rw [hn.ruv, dD.crdT_ofT, one_zsmul])
  rw [← key]; group

theorem t_conj_eq {e : G} {y : ℤ} (hn : Normal100 hS dD e y 1) :
    e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t := by
  have key : e⁻¹ * dD.t * e * dD.t⁻¹ = (dD.a : G)⁻¹ := by
    rw [dD.t100_a_inv_eq_ofT]
    exact crdT_inj dD.e hn.mem.2.2 (dD.ofT_mem _) (by rw [hn.rt, dD.crdT_ofT, one_zsmul])
  rw [← key]; group

theorem u_conj_eq {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) : e⁻¹ * dD.u * e = dD.u := by
  rw [mul_assoc, hn.comm]; group

theorem sq_eq (h : F.IsD D dD) {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) {μ : ℤ}
    (hμ : (2 : ℤ) ^ (m + 1) ∣ (y + 1) * p + 2 * μ) :
    e * e = dD.ofT (μ • Torus.ofInt (StrothTypeIndex.t100 m).k ![1, 0, 0]) :=
  (hn.mul hn).eq_ofT h (by convert hμ using 1; ring)

theorem odd {e : G} {y p : ℤ} (hn : Normal100 hS dD e y p) : Odd y := by
  rcases Int.even_or_odd y with ⟨k, rfl⟩ | hy
  · exfalso
    have h1 := dD.thetaT_inv_thetaT (hS.R_le_normalizer hn.mem.1)
      (Torus.ofInt (StrothTypeIndex.t100 m).k ![0, 2 ^ m, 0])
    rw [hn.scalar, add_zsmul, ← smul_add, Stroth32Cent.A_add_self, smul_zero, map_zero,
      eq_comm, t100_vec_eq_zero_iff] at h1
    obtain ⟨-, ⟨j, hj⟩, -⟩ := h1
    have h0 : (2 : ℤ) ^ m * (1 - 2 * j) = 0 := by linear_combination hj
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact pow_ne_zero m two_ne_zero h0
    · omega
  · exact hy

theorem sq_mem (h : F.IsD D dD) {e : G} {y : ℤ} (hn : Normal100 hS dD e y 1) : e * e ∈ D := by
  obtain ⟨k, hk⟩ := hn.odd
  exact (hn.mul hn).mem_of_two_dvd h ⟨k + 1, by rw [hk]; ring⟩

theorem mul_uv_sq_ne_one (h : F.IsD D dD) {e d : G} {y : ℤ} (hn : Normal100 hS dD e y 1)
    (hd : d ∈ D) : e * d * dD.uv * (e * d * dD.uv) ≠ 1 := by
  intro h1
  have hsq := hn.sq_mem h
  obtain ⟨-, hc⟩ := dD.crdT_sq_coset (hS.R_le_normalizer hn.mem.1) dD.uv_mem dD.uv_sq
    dD.thetaT_uv hn.mem.2.1 hsq hd
  obtain ⟨μ, hμ⟩ := t100_crdT_eq_of_proj_eq hS hsq
    (by rw [hS.proj_mul dD.ρ_mem hn.mem.1 hn.mem.1, hn.proj])
  obtain ⟨d0, d1, d2, hd'⟩ := t100_exists_vec (crdT dD.e d)
  obtain ⟨k, hk⟩ := hn.odd
  rw [h1, crdT_one, hμ, hn.scalar, hn.ruv, hd', one_zsmul, t100_zsmul_vec, t100_zsmul_vec,
    t100_φuv_vec, t100_add_vec, t100_add_vec, t100_add_vec, eq_comm, t100_vec_eq_zero_iff] at hc
  obtain ⟨-, ⟨q, hq⟩, -⟩ := hc
  rw [hk] at hq
  have h2 : (2 : ℤ) ∣ 1 := ⟨2 ^ m * q - (k * d1 + d1 - d0 + d2), by linear_combination hq⟩
  omega

theorem mul_t_sq_ne_one (h : F.IsD D dD) {e d : G} {y : ℤ} (hn : Normal100 hS dD e y 1)
    (hd : d ∈ D) : e * d * dD.t * (e * d * dD.t) ≠ 1 := by
  intro h1
  have hsq := hn.sq_mem h
  obtain ⟨-, hc⟩ := dD.crdT_sq_coset (hS.R_le_normalizer hn.mem.1) dD.t_mem dD.t_sq
    dD.thetaT_t hn.mem.2.2 hsq hd
  obtain ⟨μ, hμ⟩ := t100_crdT_eq_of_proj_eq hS hsq
    (by rw [hS.proj_mul dD.ρ_mem hn.mem.1 hn.mem.1, hn.proj])
  obtain ⟨d0, d1, d2, hd'⟩ := t100_exists_vec (crdT dD.e d)
  obtain ⟨k, hk⟩ := hn.odd
  rw [h1, crdT_one, hμ, hn.scalar, hn.rt, hd', one_zsmul, t100_zsmul_vec, t100_zsmul_vec,
    t100_φt_vec, t100_add_vec, t100_add_vec, t100_add_vec, eq_comm, t100_vec_eq_zero_iff] at hc
  obtain ⟨-, ⟨q, hq⟩, -⟩ := hc
  rw [hk] at hq
  have h2 : (2 : ℤ) ∣ 1 := ⟨k * d1 + d0 - d2 - 2 ^ m * q, by linear_combination -hq⟩
  omega

theorem rel_ii (h : F.IsD D dD) (hm : 1 ≤ m) {e : G} {y : ℤ} (hn : Normal100 hS dD e y 1)
    (hy : (2 : ℤ) ^ (m + 1) ∣ y - (1 + 2 ^ m)) :
    e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
      e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
      e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1) := by
  obtain ⟨k, hk⟩ := hy
  have hy' : (2 : ℤ) ^ (m + 1) ∣ y - (1 + ((2 ^ m : ℕ) : ℤ)) := ⟨k, by push_cast; exact hk⟩
  have h2 : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := by rw [← pow_succ']; congr 1; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hn.c_conj_eq (l := 1) ⟨2 * k + 1, by linear_combination hk⟩, one_zsmul, ← dD.t100_c_eq]
  · rw [hn.a_conj_eq hy', dD.t100_a_mul_pow_eq]
  · rw [hn.b_conj_eq hy', dD.t100_b_mul_pow_eq]
  · rw [hn.sq_eq h (μ := -1 + ((2 ^ (m - 1) : ℕ) : ℤ))
      ⟨k + 1, by push_cast; linear_combination hk + h2⟩, dD.t100_c_inv_mul_pow_eq]

theorem rel_iii (h : F.IsD D dD) {e : G} {y : ℤ} (hn : Normal100 hS dD e y 1)
    (hy : (2 : ℤ) ^ (m + 1) ∣ y + 1) :
    e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1 := by
  obtain ⟨k, hk⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hn.c_conj_eq (l := -1) ⟨2 * k, by linear_combination hk⟩, dD.t100_c_inv_eq]
  · rw [hn.a_conj_eq (l := -1) ⟨k, by linear_combination hk⟩, dD.t100_a_inv_eq]
  · rw [hn.b_conj_eq (l := -1) ⟨k, by linear_combination hk⟩, dD.t100_b_inv_eq]
  · rw [hn.sq_eq h (μ := 0) ⟨k, by linear_combination hk⟩, zero_zsmul, dD.ofT_zero]

theorem rel_iv (h : F.IsD D dD) (hm : 1 ≤ m) {e : G} {y : ℤ} (hn : Normal100 hS dD e y 1)
    (hy : (2 : ℤ) ^ (m + 1) ∣ y - (-1 + 2 ^ m)) :
    e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
      e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
      e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
      e * e = (dD.c : G) ^ 2 ^ (m - 1) := by
  obtain ⟨k, hk⟩ := hy
  have hy' : (2 : ℤ) ^ (m + 1) ∣ y - (-1 + ((2 ^ m : ℕ) : ℤ)) := ⟨k, by push_cast; exact hk⟩
  have h2 : (2 : ℤ) * 2 ^ (m - 1) = 2 ^ m := by rw [← pow_succ']; congr 1; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hn.c_conj_eq (l := -1) ⟨2 * k + 1, by linear_combination hk⟩, dD.t100_c_inv_eq]
  · rw [hn.a_conj_eq hy', dD.t100_a_inv_mul_pow_eq]
  · rw [hn.b_conj_eq hy', dD.t100_b_inv_mul_pow_eq]
  · rw [hn.sq_eq h (μ := ((2 ^ (m - 1) : ℕ) : ℤ))
      ⟨k + 1, by push_cast; linear_combination hk + h2⟩, ← dD.t100_c_pow_eq]

theorem rels (h : F.IsD D dD) (hm : 1 ≤ m) {e : G} {y : ℤ} (hn : Normal100 hS dD e y 1)
    (hy : (2 : ℤ) ^ (m + 1) ∣ y - (1 + 2 ^ m) ∨ (2 : ℤ) ^ (m + 1) ∣ y + 1 ∨
      (2 : ℤ) ^ (m + 1) ∣ y - (-1 + 2 ^ m)) :
    e⁻¹ * dD.uv * e = (dD.c : G) ^ 2 * dD.a * dD.b * dD.uv ∧
      e⁻¹ * dD.t * e = (dD.a : G)⁻¹ * dD.t ∧ e⁻¹ * dD.u * e = dD.u ∧
      ((e⁻¹ * (dD.c : G) * e = dD.c ∧ e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ m ∧
          e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ m ∧
          e * e = (dD.c : G)⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
        (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧ e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ ∧
          e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ ∧ e * e = 1) ∨
        (e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹ ∧
          e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ m ∧
          e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ m ∧
          e * e = (dD.c : G) ^ 2 ^ (m - 1))) :=
  ⟨hn.uv_conj_eq, hn.t_conj_eq, hn.u_conj_eq,
    hy.imp (hn.rel_ii h hm) (Or.imp (hn.rel_iii h) (hn.rel_iv h hm))⟩

end Normal100

namespace StrothFrame.IsD

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)}

theorem t100_exists_normal_one (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D)
    (hm : 1 ≤ m) (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {g : G}
    (hg : g ∈ hS.R1 dD.uv dD.t) (hpg : hS.proj dD.ρ g * g⁻¹ ∈ D) (hgD : g ∉ D) :
    ∃ d ∈ D, ∃ y : ℤ, Normal100 hS dD (g * d) y 1 := by
  obtain ⟨d, hd, y, p, hn⟩ := h.exists_normal100 hS hm hfus hg hpg
  have hp : ¬ (2 : ℤ) ∣ p := fun hp => hgD (by
    simpa using mul_mem (hn.mem_of_two_dvd h hp) (inv_mem hd))
  obtain ⟨d', hd', hn'⟩ := hn.renorm (p' := 1) (by
    rcases Int.even_or_odd p with hpe | ⟨q, hq⟩
    · exact absurd (even_iff_two_dvd.mp hpe) hp
    · exact ⟨q, by rw [hq]; ring⟩)
  exact ⟨d * d', mul_mem hd hd', y, by rwa [mul_assoc] at hn'⟩

theorem t100_classify_R1 (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u)
    (hρR : ∀ e ∈ hS.R1 dD.uv dD.t, hS.proj dD.ρ e * e⁻¹ ∈ D) :
    hS.R1 dD.uv dD.t = D ∨ ∃ e : G, ∃ y : ℤ, Normal100 hS dD e y 1 ∧
      hS.R1 dD.uv dD.t = D ⊔ Subgroup.zpowers e ∧
      ((2 : ℤ) ^ (m + 1) ∣ y - (1 + 2 ^ m) ∨ (2 : ℤ) ^ (m + 1) ∣ y + 1 ∨
        (2 : ℤ) ^ (m + 1) ∣ y - (-1 + 2 ^ m)) := by
  have key : ∀ g ∈ hS.R1 dD.uv dD.t, g ∉ D →
      ∃ d ∈ D, ∃ y : ℤ, Normal100 hS dD (g * d) y 1 := fun g hg hgD =>
    h.t100_exists_normal_one hS hm hfus hg (hρR g hg) hgD
  have same : ∀ f ∈ hS.R1 dD.uv dD.t, f ∉ D → ∀ g ∈ hS.R1 dD.uv dD.t, g ∉ D →
      f * g⁻¹ ∈ D := by
    intro f hf hfD g hg hgD
    obtain ⟨d₁, hd₁, y₁, hn₁⟩ := key f hf hfD
    obtain ⟨d₂, hd₂, y₂, hn₂⟩ := key g hg hgD
    have h12 := hn₁.mul_inv_mem h hn₂ (by norm_num)
    have hc : g * (d₂ * d₁⁻¹) * g⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hS.R_le_normalizer hg.1) _).mp
        (mul_mem hd₂ (inv_mem hd₁))
    have := mul_mem h12 hc
    convert this using 1
    group
  by_cases hall : ∀ g ∈ hS.R1 dD.uv dD.t, g ∈ D
  · exact Or.inl (le_antisymm (fun g hg => hall g hg) (t100_D_le_R1 hS))
  obtain ⟨g, hg, hgD⟩ : ∃ g ∈ hS.R1 dD.uv dD.t, g ∉ D := by
    by_contra hne
    exact hall fun g hg => by_contra fun hgD => hne ⟨g, hg, hgD⟩
  obtain ⟨d, hd, y, hn⟩ := key g hg hgD
  have heD : g * d ∉ D := fun h' => hgD (by simpa using mul_mem h' (inv_mem hd))
  refine Or.inr ⟨g * d, y, hn, le_antisymm (fun f hf => ?_)
    (sup_le (t100_D_le_R1 hS) (Subgroup.zpowers_le.mpr hn.mem)), ?_⟩
  · by_cases hfD : f ∈ D
    · exact Subgroup.mem_sup_left hfD
    · have := Subgroup.mul_mem_sup (same f hf hfD (g * d) hn.mem heD)
        (Subgroup.mem_zpowers (g * d))
      rwa [inv_mul_cancel_right] at this
  · have hee : g * d * (g * d) ∈ D := by
      by_contra hee
      have := same _ (mul_mem hn.mem hn.mem) hee (g * d) hn.mem heD
      rw [mul_inv_cancel_right] at this
      exact heD this
    exact t100_sq_cases hm ((hn.mul hn).scalar_dvd_of_mem hee)
      (fun hy => heD (hn.mem_of_scalar hy))

end StrothFrame.IsD

end CFSG.CGT.Stroth77
