module

public import CFSG.CGT.Stroth77.Stroth32Cent
public import CFSG.CGT.Stroth77.Stroth32H1

public section

namespace CFSG.CGT.Stroth77

namespace Stroth32V0

open Stroth42Core Stroth32H1

variable {m : ℕ}

private theorem one_mod_four {α₁ α₂ α₃ : ℤ} (h₁ : Odd α₁) (h₂ : (4 : ℤ) ∣ α₂ - α₁)
    (h₃ : (4 : ℤ) ∣ α₃ - α₁) (h : (4 : ℤ) ∣ α₁ * α₂ * α₃ - 1) : (4 : ℤ) ∣ α₁ - 1 := by
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  obtain ⟨k₃, hk₃⟩ := h₃
  obtain ⟨K, hK⟩ := h
  rcases Int.even_or_odd a with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨b, by ring⟩
  · exfalso
    obtain ⟨z, hz⟩ : ∃ z : ℤ, (2 : ℤ) = 4 * z :=
      ⟨K - (16 * b ^ 3 + 36 * b ^ 2 + 27 * b + 6 + (4 * b + 3) ^ 2 * (k₂ + k₃) +
        4 * (4 * b + 3) * k₂ * k₃), by
        have e₂ : α₂ = 4 * b + 3 + 4 * k₂ := by linear_combination hk₂
        have e₃ : α₃ = 4 * b + 3 + 4 * k₃ := by linear_combination hk₃
        rw [e₂, e₃] at hK
        linear_combination hK⟩
    omega

private theorem dvd_sub_one_of_sq {n : ℕ} {α : ℤ} (h4 : (4 : ℤ) ∣ α - 1)
    (hsq : (2 : ℤ) ^ (n + 2 + 1) ∣ α * α - 1) : (2 : ℤ) ^ (n + 2) ∣ α - 1 := by
  obtain ⟨j, hj⟩ := h4
  have h8 : (8 : ℤ) * 2 ^ n ∣ 8 * (j * (2 * j + 1)) := by
    have e₁ : (2 : ℤ) ^ (n + 2 + 1) = 8 * 2 ^ n := by ring
    have e₂ : α * α - 1 = 8 * (j * (2 * j + 1)) := by
      rw [show α = 4 * j + 1 by linear_combination hj]; ring
    rwa [e₁, e₂] at hsq
  have hcop : IsCoprime ((2 : ℤ) ^ n) (2 * j + 1) := IsCoprime.pow_left ⟨-j, 1, by ring⟩
  obtain ⟨k, hk⟩ :=
    hcop.dvd_of_dvd_mul_right ((mul_dvd_mul_iff_left (by norm_num : (8 : ℤ) ≠ 0)).mp h8)
  exact ⟨k, by rw [hj, hk]; ring⟩

private theorem two_dvd_of_dvd_mul {n : ℕ} {x : ℤ}
    (h : (2 : ℤ) ^ (n + 2 + 1) ∣ 2 ^ (n + 2) * x) : (2 : ℤ) ∣ x := by
  rw [pow_succ] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp h

private theorem four_dvd_of_dvd {n : ℕ} {x y : ℤ}
    (h : (2 : ℤ) ^ (n + 2 + 1) ∣ 2 ^ (n + 1) * (x + 2 ^ (n + 2) * y)) : (4 : ℤ) ∣ x := by
  rw [show (2 : ℤ) ^ (n + 2 + 1) = 2 ^ (n + 1) * 4 by ring] at h
  have h' := (mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp h
  have := dvd_sub h' (⟨2 ^ n * y, by ring⟩ : (4 : ℤ) ∣ 2 ^ (n + 2) * y)
  simpa using this

private theorem sq_dvd_of {n : ℕ} {α s X : ℤ} (hα : Odd α)
    (hX : X = α * (α + 2 ^ (n + 2) * s) + 2 ^ (n + 2) * s) (h : (2 : ℤ) ^ (n + 2 + 1) ∣ 1 - X) :
    (2 : ℤ) ^ (n + 2 + 1) ∣ α * α - 1 := by
  obtain ⟨a, rfl⟩ := hα
  have := dvd_sub (dvd_neg.mpr h) (dvd_mul_right ((2 : ℤ) ^ (n + 2 + 1)) ((a + 1) * s))
  convert this using 1
  rw [hX]
  ring

private theorem φρ_cab : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![1, 1, 1]) =
    -Torus.ofInt _ ![1, 1, 0] := by
  rw [t100_φρ_vec, t100_neg_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

private theorem φρ_ca : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![1, 1, 0]) =
    Torus.ofInt _ ![1, 0, 1] := by
  rw [t100_φρ_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

private theorem φρ_cb : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![1, 0, 1]) =
    -Torus.ofInt _ ![1, 1, 1] := by
  rw [t100_φρ_vec, t100_neg_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

private theorem φρ_A : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![0, 2 ^ m, 0]) =
    Torus.ofInt _ ![0, 0, 2 ^ m] := by
  rw [t100_φρ_vec, t100_vec_eq_iff]
  exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩

private theorem φρ_B : (StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ ![0, 0, 2 ^ m]) =
    Torus.ofInt _ ![0, 2 ^ m, 0] + Torus.ofInt _ ![0, 0, 2 ^ m] := by
  rw [t100_φρ_vec, t100_add_vec, t100_vec_eq_iff]
  exact ⟨⟨2, by ring⟩, ⟨1, by ring⟩, ⟨1, by ring⟩⟩

private theorem t100_V0_unipotent {n : ℕ}
    (θ : Torus (StrothTypeIndex.t100 (n + 2)).k →+ Torus (StrothTypeIndex.t100 (n + 2)).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t100 (n + 2)).action.φuv x) =
      (StrothTypeIndex.t100 (n + 2)).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t100 (n + 2)).action.φt x) =
      (StrothTypeIndex.t100 (n + 2)).action.φt (θ x))
    (hΩ : ∀ x, x + x = 0 → θ x = x) (hsq : ∀ x, θ (θ x) = x)
    (hN : ∀ x, θ ((StrothTypeIndex.t100 (n + 2)).action.φρ
      ((StrothTypeIndex.t100 (n + 2)).action.φρ (θ ((StrothTypeIndex.t100 (n + 2)).action.φρ
        ((StrothTypeIndex.t100 (n + 2)).action.φρ (θ ((StrothTypeIndex.t100 (n + 2)).action.φρ
          ((StrothTypeIndex.t100 (n + 2)).action.φρ x)))))))) = x) :
    (∃ P Q : ℤ, θ (Torus.ofInt _ ![1, 1, 1]) = Torus.ofInt _ ![1, 1, 1] +
        P • Torus.ofInt _ ![0, 2 ^ (n + 2), 0] + Q • Torus.ofInt _ ![0, 0, 2 ^ (n + 2)]) ∧
      (∃ P Q : ℤ, θ (Torus.ofInt _ ![1, 1, 0]) = Torus.ofInt _ ![1, 1, 0] +
        P • Torus.ofInt _ ![0, 2 ^ (n + 2), 0] + Q • Torus.ofInt _ ![0, 0, 2 ^ (n + 2)]) ∧
      (∃ P Q : ℤ, θ (Torus.ofInt _ ![1, 0, 1]) = Torus.ofInt _ ![1, 0, 1] +
        P • Torus.ofInt _ ![0, 2 ^ (n + 2), 0] + Q • Torus.ofInt _ ![0, 0, 2 ^ (n + 2)]) := by
  obtain ⟨⟨α₁, s₁, r₁, o₁, h₁⟩, ⟨α₂, s₂, r₂, o₂, h₂⟩, ⟨α₃, s₃, r₃, o₃, h₃⟩⟩ :=
    Stroth32Cent.images (by omega) θ huv ht hΩ
  have hθA := hΩ _ (Stroth32Cent.A_add_self (m := n + 2))
  have hθB := hΩ _ (Stroth32Cent.B_add_self (m := n + 2))
  have hc : Torus.ofInt (StrothTypeIndex.t100 (n + 2)).k ![2 ^ (n + 1), 0, 0] =
      (2 ^ (n + 1) : ℤ) • (Torus.ofInt _ ![1, 1, 0] + Torus.ofInt _ ![1, 0, 1] -
        Torus.ofInt _ ![1, 1, 1]) := by
    rw [t100_add_vec, t100_sub_vec, t100_zsmul_vec, t100_vec_eq_iff]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  have hc2 : Torus.ofInt (StrothTypeIndex.t100 (n + 2)).k ![2 ^ (n + 1), 0, 0] +
      Torus.ofInt _ ![2 ^ (n + 1), 0, 0] = 0 := by
    rw [t100_add_vec, t100_vec_eq_zero_iff]
    exact ⟨⟨1, by ring⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
  have F1 := hΩ _ hc2
  rw [hc, map_zsmul, map_sub, map_add, h₁, h₂, h₃] at F1
  simp only [t100_zsmul_vec, t100_add_vec, t100_sub_vec] at F1
  rw [t100_vec_eq_iff] at F1
  have h21 : (4 : ℤ) ∣ α₂ - α₁ := four_dvd_of_dvd (y := s₂ + s₃ - s₁) (n := n)
    (by rw [← dvd_neg]; convert F1.2.1 using 1; ring)
  have h31 : (4 : ℤ) ∣ α₃ - α₁ := four_dvd_of_dvd (y := r₂ + r₃ - r₁) (n := n)
    (by rw [← dvd_neg]; convert F1.2.2 using 1; ring)
  have F2 := hN (Torus.ofInt _ ![1, 1, 1])
  simp only [φρ_cab, φρ_ca, φρ_cb, φρ_A, φρ_B, map_neg, map_add, map_zsmul, h₁, h₂, h₃, hθA,
    hθB] at F2
  simp only [t100_zsmul_vec, t100_add_vec, t100_neg_vec] at F2
  rw [t100_vec_eq_iff] at F2
  have h123 : (4 : ℤ) ∣ α₁ * α₂ * α₃ - 1 := by
    have := dvd_trans (⟨2 ^ n, by ring⟩ : (4 : ℤ) ∣ 2 ^ (n + 2)) F2.1
    rw [← dvd_neg]
    convert this using 1
    ring
  have h41 := one_mod_four o₁ h21 h31 h123
  have h42 : (4 : ℤ) ∣ α₂ - 1 := by
    have := dvd_add h21 h41
    convert this using 1
    ring
  have h43 : (4 : ℤ) ∣ α₃ - 1 := by
    have := dvd_add h31 h41
    convert this using 1
    ring
  have F3₁ := hsq (Torus.ofInt _ ![1, 1, 1])
  have F3₂ := hsq (Torus.ofInt _ ![1, 1, 0])
  have F3₃ := hsq (Torus.ofInt _ ![1, 0, 1])
  simp only [map_add, map_zsmul, h₁, h₂, h₃, hθA, hθB] at F3₁ F3₂ F3₃
  simp only [t100_zsmul_vec, t100_add_vec] at F3₁ F3₂ F3₃
  rw [t100_vec_eq_iff] at F3₁ F3₂ F3₃
  obtain ⟨k₁, hk₁⟩ := dvd_sub_one_of_sq h41 (sq_dvd_of (s := s₁) o₁ (by ring) F3₁.2.1)
  obtain ⟨k₂, hk₂⟩ := dvd_sub_one_of_sq h42 (sq_dvd_of (s := s₂) o₂ (by ring) F3₂.2.1)
  obtain ⟨k₃, hk₃⟩ := dvd_sub_one_of_sq h43 (sq_dvd_of (s := r₃) o₃ (by ring) F3₃.2.2)
  refine ⟨⟨k₁ + s₁, k₁ + r₁, ?_⟩, ⟨k₂ + s₂, r₂, ?_⟩, ⟨s₃, k₃ + r₃, ?_⟩⟩
  · rw [h₁]
    simp only [t100_zsmul_vec, t100_add_vec]
    rw [t100_vec_eq_iff]
    exact ⟨⟨-k₁, by linear_combination -hk₁⟩, ⟨0, by linear_combination -hk₁⟩,
      ⟨0, by linear_combination -hk₁⟩⟩
  · rw [h₂]
    simp only [t100_zsmul_vec, t100_add_vec]
    rw [t100_vec_eq_iff]
    exact ⟨⟨-k₂, by linear_combination -hk₂⟩, ⟨0, by linear_combination -hk₂⟩, ⟨0, by ring⟩⟩
  · rw [h₃]
    simp only [t100_zsmul_vec, t100_add_vec]
    rw [t100_vec_eq_iff]
    exact ⟨⟨-k₃, by linear_combination -hk₃⟩, ⟨0, by ring⟩, ⟨0, by linear_combination -hk₃⟩⟩

theorem t100_V0 (hm : 2 ≤ m)
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k)
    (huv : ∀ x, θ ((StrothTypeIndex.t100 m).action.φuv x) =
      (StrothTypeIndex.t100 m).action.φuv (θ x))
    (ht : ∀ x, θ ((StrothTypeIndex.t100 m).action.φt x) =
      (StrothTypeIndex.t100 m).action.φt (θ x))
    (hu : ∀ x, θ ((StrothTypeIndex.t100 m).action.φu x) =
      (StrothTypeIndex.t100 m).action.φu (θ x))
    (hΩ : ∀ x, x + x = 0 → θ x = x) (hsq : ∀ x, θ (θ x) = x)
    (hN : ∀ x, θ ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ
      (θ ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ
        (θ ((StrothTypeIndex.t100 m).action.φρ ((StrothTypeIndex.t100 m).action.φρ x)))))))) = x) :
    ∃ ε₁ ε₃ : ℤ, ∀ v : Fin 3 → ℤ, θ (Torus.ofInt _ v) =
      Torus.ofInt _ ![v 0, v 1 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 2),
        v 2 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 1)] := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨⟨P₁, Q₁, g₁⟩, ⟨P₂, Q₂, g₂⟩, ⟨P₃, Q₃, g₃⟩⟩ := t100_V0_unipotent θ huv ht hΩ hsq hN
  have hθA := hΩ _ (Stroth32Cent.A_add_self (m := n + 2))
  have hθB := hΩ _ (Stroth32Cent.B_add_self (m := n + 2))
  have U₁ := hu (Torus.ofInt _ ![1, 1, 1])
  have U₂ := hu (Torus.ofInt _ ![1, 1, 0])
  rw [t100_φu_vec] at U₁ U₂
  rw [g₁] at U₁
  rw [g₃, g₂] at U₂
  simp only [map_add, map_zsmul, t100_φu_vec] at U₁ U₂
  simp only [t100_zsmul_vec, t100_add_vec] at U₁ U₂
  rw [t100_vec_eq_iff] at U₁ U₂
  have hU₁ : (2 : ℤ) ∣ Q₁ - P₁ := two_dvd_of_dvd_mul (by convert U₁.2.1 using 1; ring)
  have hU₂a : (2 : ℤ) ∣ Q₂ - P₃ := two_dvd_of_dvd_mul (by convert U₂.2.1 using 1; ring)
  have hU₂b : (2 : ℤ) ∣ P₂ - Q₃ := two_dvd_of_dvd_mul (by convert U₂.2.2 using 1; ring)
  have N₁ := hN (Torus.ofInt _ ![1, 1, 1])
  simp only [φρ_cab, φρ_ca, φρ_cb, φρ_A, φρ_B, map_neg, map_add, map_zsmul, g₁, g₂, g₃, hθA,
    hθB] at N₁
  simp only [t100_zsmul_vec, t100_add_vec, t100_neg_vec] at N₁
  rw [t100_vec_eq_iff] at N₁
  have hN₁ : (2 : ℤ) ∣ P₂ + Q₂ + 2 * P₃ + 3 * Q₃ - P₁ :=
    two_dvd_of_dvd_mul (by convert N₁.2.1 using 1; ring)
  have hQ₃ : (2 : ℤ) ∣ Q₃ - P₂ := by
    have := dvd_neg.mpr hU₂b
    convert this using 1
    ring
  have hP₃ : (2 : ℤ) ∣ P₃ - Q₂ := by
    have := dvd_neg.mpr hU₂a
    convert this using 1
    ring
  have hP₁ : (2 : ℤ) ∣ P₁ - Q₂ := by
    have := dvd_add (dvd_add (dvd_neg.mpr hN₁) (hQ₃.mul_left 3))
      (dvd_mul_right (2 : ℤ) (2 * P₂ + P₃))
    convert this using 1
    ring
  have hQ₁ : (2 : ℤ) ∣ Q₁ - Q₂ := by
    have := dvd_add hU₁ hP₁
    convert this using 1
    ring
  refine ⟨P₂, Q₂ - P₂, fun v => ?_⟩
  have hx : Torus.ofInt (StrothTypeIndex.t100 (n + 2)).k v =
      (v 1 + v 2 - v 0) • Torus.ofInt _ ![1, 1, 1] + (v 0 - v 2) • Torus.ofInt _ ![1, 1, 0] +
        (v 0 - v 1) • Torus.ofInt _ ![1, 0, 1] := by
    rw [← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_zsmul, ← Torus.ofInt_add,
      ← Torus.ofInt_add]
    congr 1; funext i; fin_cases i <;> simp
  rw [hx]
  simp only [map_add, map_zsmul, g₁, g₂, g₃]
  simp only [t100_zsmul_vec, t100_add_vec]
  rw [t100_vec_eq_iff]
  refine ⟨⟨0, by ring⟩, ?_, ?_⟩
  · have key : (2 : ℤ) ^ (n + 2 + 1) ∣
        2 ^ (n + 2) * (-(v 1 + v 2 - v 0) * (P₁ - Q₂) - (v 0 - v 1) * (P₃ - Q₂)) := by
      rw [pow_succ]
      exact mul_dvd_mul_left _ (dvd_sub (hP₁.mul_left _) (hP₃.mul_left _))
    convert key using 1
    ring
  · have key : (2 : ℤ) ^ (n + 2 + 1) ∣
        2 ^ (n + 2) * (-(v 1 + v 2 - v 0) * (Q₁ - Q₂) - (v 0 - v 1) * (Q₃ - P₂)) := by
      rw [pow_succ]
      exact mul_dvd_mul_left _ (dvd_sub (hQ₁.mul_left _) (hQ₃.mul_left _))
    convert key using 1
    ring

end Stroth32V0

end CFSG.CGT.Stroth77
