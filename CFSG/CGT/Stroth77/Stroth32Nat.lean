module

public import CFSG.CGT.Stroth77.Stroth32H1

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth32H1

namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m))

theorem t100_exists_u_comm (hm : 1 ≤ m)
    (hfus : ∀ g : G, g⁻¹ * dD.u * g ≠ (dD.c : G) ^ 2 ^ (m - 1) * dD.u) {f : G}
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hu : dD.u⁻¹ * f * dD.u * f⁻¹ ∈ D) :
    ∃ d ∈ D, dD.u * (f * d) = f * d * dD.u := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  set s := f⁻¹ * (dD.u⁻¹ * f * dD.u) with hs
  have hsD : s ∈ D := by
    have := (Subgroup.mem_normalizer_iff''.mp hfN _).mp hu
    convert this using 1
    rw [hs]; group
  have hsu : s * (dD.u⁻¹ * s * dD.u) = 1 := by
    rw [hs]
    calc f⁻¹ * (dD.u⁻¹ * f * dD.u) * (dD.u⁻¹ * (f⁻¹ * (dD.u⁻¹ * f * dD.u)) * dD.u)
        = f⁻¹ * (dD.u * dD.u)⁻¹ * f * (dD.u * dD.u) := by group
      _ = 1 := by rw [dD.u_sq]; group
  have hus : dD.u⁻¹ * s * dD.u ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.u_mem _).mp hsD
  have h2 : crdT dD.e s + (StrothTypeIndex.t100 (n + 1)).action.φu (crdT dD.e s) = 0 := by
    have := congrArg (crdT dD.e) hsu
    rwa [crdT_mul dD.e hsD hus, crdT_conj dD.e dD.u_mem dD.u_conj hsD, crdT_one] at this
  obtain ⟨w, hw⟩ := Torus.exists_ofInt (crdT dD.e s)
  rw [← hw, t100_φu, ← Torus.ofInt_add, t100_ofInt_eq_zero_iff] at h2
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h2
  obtain ⟨⟨j, hj⟩, ⟨k, hk⟩, -⟩ := h2
  set d := dD.ofT (Torus.ofInt (StrothTypeIndex.t100 (n + 1)).k ![0, w 1, 0]) with hd
  have hdD : d ∈ D := dD.ofT_mem _
  have hud : dD.u⁻¹ * d * dD.u ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.u_mem _).mp hdD
  have hX : (f * d)⁻¹ * (dD.u⁻¹ * (f * d) * dD.u) = d⁻¹ * s * (dD.u⁻¹ * d * dD.u) := by
    rw [hs]; group
  have hXD : d⁻¹ * s * (dD.u⁻¹ * d * dD.u) ∈ D := mul_mem (mul_mem (inv_mem hdD) hsD) hud
  have hcrd : crdT dD.e (d⁻¹ * s * (dD.u⁻¹ * d * dD.u)) = Torus.ofInt _ ![w 0, 0, 0] := by
    rw [crdT_mul dD.e (mul_mem (inv_mem hdD) hsD) hud, crdT_mul dD.e (inv_mem hdD) hsD,
      crdT_inv dD.e hdD, crdT_conj dD.e dD.u_mem dD.u_conj hdD, hd, dD.crdT_ofT, ← hw, t100_φu,
      ← Torus.ofInt_neg, ← Torus.ofInt_add, ← Torus.ofInt_add, t100_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨-k, by linear_combination -hk⟩⟩
  rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  ·
    have hw0 : w 0 = 2 ^ (n + 1) * i :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hj + 2 ^ (n + 1) * hi)
    have h0 : Torus.ofInt (StrothTypeIndex.t100 (n + 1)).k ![w 0, 0, 0] = 0 := by
      rw [t100_vec_eq_zero_iff]
      exact ⟨⟨i, hw0⟩, dvd_zero _, dvd_zero _⟩
    have hX1 : (f * d)⁻¹ * (dD.u⁻¹ * (f * d) * dD.u) = 1 := by
      rw [hX]
      exact crdT_inj dD.e hXD (one_mem D) (by rw [hcrd, h0, crdT_one])
    refine ⟨d, hdD, ?_⟩
    rw [inv_mul_eq_one] at hX1
    calc dD.u * (f * d) = dD.u * (dD.u⁻¹ * (f * d) * dD.u) := by rw [← hX1]
      _ = f * d * dD.u := by group
  ·
    exfalso
    have hw0 : w 0 = 2 ^ (n + 1) * i + 2 ^ n :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hj + 2 ^ (n + 1) * hi)
    have hc₁D : (dD.c : G) ^ 2 ^ (n + 1 - 1) ∈ D := D.pow_mem dD.c.2 _
    have hc₁ : crdT dD.e ((dD.c : G) ^ 2 ^ (n + 1 - 1)) = Torus.ofInt _ ![w 0, 0, 0] := by
      have e1 : crdT dD.e ((dD.c : G) ^ 2 ^ (n + 1 - 1)) = om100 (n + 1) ![1, 0, 0] := by
        rw [dD.t100_c_pow]
        exact dD.crdT_ofT _
      rw [e1, om100_succ, t100_ofInt_eq_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      exact ⟨⟨i, by linear_combination hw0⟩, ⟨0, by ring⟩, ⟨0, by ring⟩⟩
    have hXc : (f * d)⁻¹ * (dD.u⁻¹ * (f * d) * dD.u) = (dD.c : G) ^ 2 ^ (n + 1 - 1) := by
      rw [hX]
      exact crdT_inj dD.e hXD hc₁D (hcrd.trans hc₁.symm)
    have huc : dD.u⁻¹ * (dD.c : G) ^ 2 ^ (n + 1 - 1) * dD.u = (dD.c : G) ^ 2 ^ (n + 1 - 1) := by
      rw [dD.t100_c_pow, dD.conj_ofTorus dD.u_mem dD.u_conj, t100_φu_om]
      rfl
    have hc1i : ((dD.c : G) ^ 2 ^ (n + 1 - 1))⁻¹ = (dD.c : G) ^ 2 ^ (n + 1 - 1) :=
      inv_eq_of_mul_eq_one_right (Stroth43Fus.t100_c₁_mul_self dD (by omega))
    apply hfus (f * d)
    calc (f * d)⁻¹ * dD.u * (f * d)
        = dD.u * ((f * d)⁻¹ * (dD.u⁻¹ * (f * d) * dD.u))⁻¹ := by group
      _ = dD.u * (dD.c : G) ^ 2 ^ (n + 1 - 1) := by rw [hXc, hc1i]
      _ = (dD.c : G) ^ 2 ^ (n + 1 - 1) * dD.u := by
        conv_lhs => rw [← huc]
        group

end StrothWeakTypeData

namespace Stroth32Nat

variable {m : ℕ}

theorem cast_zero_of_eq_two_mul {a z : ℤ} (h : a = 2 * z) : ((a : ℤ) : ZMod 2) = 0 :=
  ZMod.intCast_eq_zero_iff_even.2 ⟨z, by rw [h]; ring⟩

theorem t100_sq_par (hm : 2 ≤ m)
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k) (ε₁ ε₃ : ℤ)
    (hθ : ∀ v : Fin 3 → ℤ, θ (Torus.ofInt _ v) =
      Torus.ofInt _ ![v 0, v 1 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 2), v 2 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 1)])
    (x y w : Fin 3 → ℤ) (hw : θ (Torus.ofInt _ w) = Torus.ofInt _ w)
    (h1 : θ (Torus.ofInt _ x) + Torus.ofInt _ x =
      (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ w) - Torus.ofInt _ w)
    (h2 : θ (Torus.ofInt _ y) + Torus.ofInt _ y =
      (StrothTypeIndex.t100 m).action.φt (Torus.ofInt _ w) - Torus.ofInt _ w)
    (hx1 : Odd (x 1)) (hy0 : Odd (y 0)) : Even ε₃ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [hθ] at hw h1 h2
  rw [t100_φuv, ← Torus.ofInt_add, ← Torus.ofInt_sub, t100_ofInt_eq_iff] at h1
  rw [t100_φt, ← Torus.ofInt_add, ← Torus.ofInt_sub, t100_ofInt_eq_iff] at h2
  rw [t100_ofInt_eq_iff] at hw
  simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2 hw
  obtain ⟨-, ⟨k1, f1⟩, -⟩ := h1
  obtain ⟨⟨k0, f0⟩, -, -⟩ := h2
  obtain ⟨-, ⟨k4, f4⟩, -⟩ := hw
  have F1 : x 1 + w 0 - w 2 = 2 * (-(2 ^ n * (ε₁ * x 0 + ε₃ * x 2)) - 2 ^ (n + 1) * k1) :=
    mul_left_cancel₀ two_ne_zero (by linear_combination -f1)
  have F3 : y 0 + w 2 = 2 * (-(2 ^ n * k0)) :=
    mul_left_cancel₀ two_ne_zero (by linear_combination -f0)
  have F4 : ε₁ * w 0 + ε₃ * w 2 = 2 * (-k4) :=
    mul_left_cancel₀ (pow_ne_zero (n + 2) (two_ne_zero : (2 : ℤ) ≠ 0))
      (by linear_combination -f4)
  have G1 := cast_zero_of_eq_two_mul F1
  have G3 := cast_zero_of_eq_two_mul F3
  have G4 := cast_zero_of_eq_two_mul F4
  push_cast at G1 G3 G4
  rw [← ZMod.intCast_eq_zero_iff_even]
  have k1 : ∀ Y W2 : ZMod 2, Y + W2 = 0 → Y = 1 → W2 = 1 := by decide
  have k2 : ∀ A W0 W2 : ZMod 2, A + W0 - W2 = 0 → A = 1 → W2 = 1 → W0 = 0 := by decide
  have k3 : ∀ E1 E3 W0 W2 : ZMod 2, E1 * W0 + E3 * W2 = 0 → W0 = 0 → W2 = 1 → E3 = 0 := by
    decide
  have hW2 := k1 _ _ G3 (ZMod.intCast_eq_one_iff_odd.2 hy0)
  exact k3 _ _ _ _ G4 (k2 _ _ _ G1 (ZMod.intCast_eq_one_iff_odd.2 hx1) hW2) hW2

theorem t100_theta_rho_form
    (θ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k) (ε₁ ε₃ : ℤ)
    (hθ : ∀ v : Fin 3 → ℤ, θ (Torus.ofInt _ v) =
      Torus.ofInt _ ![v 0, v 1 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 2), v 2 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 1)])
    (v : Fin 3 → ℤ) :
    (StrothTypeIndex.t100 m).action.φρ (θ ((StrothTypeIndex.t100 m).action.φρ
      ((StrothTypeIndex.t100 m).action.φρ (Torus.ofInt _ v)))) =
      Torus.ofInt _ ![v 0, v 1 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 1 + ε₃ * v 2),
        v 2 + 2 ^ m * (ε₃ * v 2)] := by
  rw [t100_φρ, t100_φρ, hθ, t100_φρ, t100_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  exact ⟨⟨2 * (ε₁ * (v 0 - 2 * v 1) + ε₃ * (v 2 - v 1)), by ring⟩,
    ⟨ε₁ * v 0 - ε₁ * v 1 + ε₃ * v 2, by ring⟩, ⟨ε₃ * v 2, by ring⟩⟩

theorem t100_urel_par (hm : 1 ≤ m)
    (θ₂ : Torus (StrothTypeIndex.t100 m).k →+ Torus (StrothTypeIndex.t100 m).k) (ε₁ ε₃ : ℤ)
    (hθ₂ : ∀ v : Fin 3 → ℤ, θ₂ (Torus.ofInt _ v) =
      Torus.ofInt _ ![v 0, v 1 + 2 ^ m * (ε₁ * v 0 + ε₃ * v 1 + ε₃ * v 2),
        v 2 + 2 ^ m * (ε₃ * v 2)])
    (x y : Fin 3 → ℤ) {κ₂ κ₃ : ℤ} (e2 : y 2 = y 0 + 2 ^ m * κ₂)
    (e3 : y 0 - y 1 = x 2 + 2 ^ m * κ₃)
    (hu : (StrothTypeIndex.t100 m).action.φu (Torus.ofInt _ x +
      (StrothTypeIndex.t100 m).action.φuv (Torus.ofInt _ y)) = Torus.ofInt _ y)
    (x' y' z : Torus (StrothTypeIndex.t100 m).k)
    (h1 : (StrothTypeIndex.t100 m).action.φu x' = θ₂ (Torus.ofInt _ x) + x' +
      ((StrothTypeIndex.t100 m).action.φuv z - z))
    (h2 : (StrothTypeIndex.t100 m).action.φu (x' + (StrothTypeIndex.t100 m).action.φuv y') =
      θ₂ (Torus.ofInt _ y) + y' + ((StrothTypeIndex.t100 m).action.φt z - z))
    (hx2 : Odd (x 2)) (hy0 : Odd (y 0)) : Even (ε₁ + ε₃) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨p, rfl⟩ := Torus.exists_ofInt x'
  obtain ⟨q, rfl⟩ := Torus.exists_ofInt y'
  obtain ⟨r, rfl⟩ := Torus.exists_ofInt z
  simp only [hθ₂, t100_φu, t100_φuv, t100_φt, ← Torus.ofInt_add, ← Torus.ofInt_sub] at h1 h2 hu
  rw [t100_ofInt_eq_iff] at h1 h2 hu
  simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2 hu
  obtain ⟨-, -, ⟨a2, g2⟩⟩ := h1
  obtain ⟨-, ⟨b1, f1⟩, ⟨b2, f2⟩⟩ := h2
  obtain ⟨-, ⟨c1, hc1⟩, -⟩ := hu
  have F : ε₁ * y 0 + ε₃ * y 1 + ε₃ * x 2 = 2 * (b1 - b2 + a2 + c1 + κ₂) :=
    mul_left_cancel₀ (pow_ne_zero (n + 1) (two_ne_zero : (2 : ℤ) ≠ 0))
      (by linear_combination f1 - f2 + g2 + hc1 + 2 * e2)
  have E3 : y 0 - y 1 - x 2 = 2 * (2 ^ n * κ₃) := by linear_combination e3
  have G := cast_zero_of_eq_two_mul F
  have H := cast_zero_of_eq_two_mul E3
  push_cast at G H
  rw [← ZMod.intCast_eq_zero_iff_even]
  push_cast
  have k1 : ∀ Y0 Y1 X2 : ZMod 2, Y0 - Y1 - X2 = 0 → Y0 = 1 → X2 = 1 → Y1 = 0 := by decide
  have k2 : ∀ E1 E3 Y0 Y1 X2 : ZMod 2, E1 * Y0 + E3 * Y1 + E3 * X2 = 0 → Y0 = 1 → Y1 = 0 →
      X2 = 1 → E1 + E3 = 0 := by
    intro E1 E3 Y0 Y1 X2 h h0 h1 h2
    rw [h0, h1, h2] at h
    simpa using h
  have hy0' := ZMod.intCast_eq_one_iff_odd.2 hy0
  have hx2' := ZMod.intCast_eq_one_iff_odd.2 hx2
  exact k2 _ _ _ _ _ G hy0' (k1 _ _ _ H hy0' hx2') hx2'

end Stroth32Nat

end CFSG.CGT.Stroth77
