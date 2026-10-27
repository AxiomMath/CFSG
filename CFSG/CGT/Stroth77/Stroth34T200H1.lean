module

public import CFSG.CGT.Stroth77.Stroth34T200Coord

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T200

variable {m : ℕ}

theorem t200_cocycle_ints (x y : Fin 3 → ℤ)
    (h1 : Torus.ofInt (StrothTypeIndex.t200 m).k x +
      (StrothTypeIndex.t200 m).action.φuv (Torus.ofInt _ x) = 0)
    (h2 : Torus.ofInt (StrothTypeIndex.t200 m).k y +
      (StrothTypeIndex.t200 m).action.φt (Torus.ofInt _ y) = 0)
    (h3 : Torus.ofInt (StrothTypeIndex.t200 m).k x +
      (StrothTypeIndex.t200 m).action.φuv (Torus.ofInt _ y) =
      Torus.ofInt _ y + (StrothTypeIndex.t200 m).action.φt (Torus.ofInt _ x)) :
    ∃ κ₁ κ₂ κ₃ : ℤ, x 1 + x 2 = 2 * x 0 + 2 * 2 ^ m * κ₁ ∧
      y 2 = 2 * y 0 + 2 * 2 ^ m * κ₂ ∧ x 2 + y 1 = 2 * y 0 + 2 * 2 ^ m * κ₃ := by
  simp only [t200_φuv, t200_φt, ← Torus.ofInt_add] at h1 h2 h3
  rw [t200_ofInt_eq_zero_iff] at h1 h2
  rw [t200_ofInt_eq_iff] at h3
  simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3
  obtain ⟨-, ⟨k1, e1⟩, -⟩ := h1
  obtain ⟨-, ⟨k2, e2⟩, -⟩ := h2
  obtain ⟨-, -, ⟨k3, e3⟩⟩ := h3
  refine ⟨k1, -k2, -k3, ?_, ?_, ?_⟩
  · have h : 2 * (x 1 + x 2) = 2 * (2 * x 0 + 2 * 2 ^ m * k1) := by linear_combination e1
    exact mul_left_cancel₀ two_ne_zero h
  · have h : 2 * y 2 = 2 * (2 * y 0 + 2 * 2 ^ m * -k2) := by linear_combination -e2
    exact mul_left_cancel₀ two_ne_zero h
  · have h : 2 * (x 2 + y 1) = 2 * (2 * y 0 + 2 * 2 ^ m * -k3) := by linear_combination -e3
    exact mul_left_cancel₀ two_ne_zero h

theorem t200_rho_triv (ruv rt : Torus (StrothTypeIndex.t200 m).k)
    (h1 : ruv + (StrothTypeIndex.t200 m).action.φuv ruv = 0)
    (h2 : rt + (StrothTypeIndex.t200 m).action.φt rt = 0)
    (h3 : ruv + (StrothTypeIndex.t200 m).action.φuv rt =
      rt + (StrothTypeIndex.t200 m).action.φt ruv) :
    ∃ d₀ : Torus (StrothTypeIndex.t200 m).k,
      (StrothTypeIndex.t200 m).action.φρ (ruv + (StrothTypeIndex.t200 m).action.φuv rt) =
          ruv - d₀ + (StrothTypeIndex.t200 m).action.φuv d₀ ∧
        (StrothTypeIndex.t200 m).action.φρ ruv =
          rt - d₀ + (StrothTypeIndex.t200 m).action.φt d₀ := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt ruv
  obtain ⟨y, rfl⟩ := Torus.exists_ofInt rt
  obtain ⟨κ₁, κ₂, κ₃, e1, e2, e3⟩ := t200_cocycle_ints x y h1 h2 h3
  refine ⟨Torus.ofInt _ ![y 0 + 2 ^ m * (2 * κ₂ - κ₃),
      -x 0 + x 1 + 2 * y 0 + 2 ^ m * (-κ₁ + 3 * κ₂ - κ₃),
      x 0 - x 1 + y 0 + 2 ^ m * (κ₁ + 3 * κ₂ - 2 * κ₃)], ?_, ?_⟩
  · simp only [t200_φuv, t200_φρ, ← Torus.ofInt_add, ← Torus.ofInt_sub]
    rw [t200_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨-2 * κ₂ + 3 * κ₃, by linear_combination e3⟩,
      ⟨κ₃, by linear_combination -e1 + e2 + 2 * e3⟩,
      ⟨-κ₂ + κ₃, by linear_combination e1 - e2 + e3⟩⟩
  · simp only [t200_φt, t200_φρ, ← Torus.ofInt_add, ← Torus.ofInt_sub]
    rw [t200_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨κ₁ - 3 * κ₂ + 2 * κ₃, by linear_combination e1⟩,
      ⟨-κ₂ + κ₃, by linear_combination e3⟩,
      ⟨-κ₂ + κ₃, by linear_combination e1 + e2⟩⟩

theorem t200_u_triv (hm : 1 ≤ m) (ruv rt : Torus (StrothTypeIndex.t200 m).k)
    (h1 : ruv + (StrothTypeIndex.t200 m).action.φuv ruv = 0)
    (h2 : rt + (StrothTypeIndex.t200 m).action.φt rt = 0)
    (h3 : ruv + (StrothTypeIndex.t200 m).action.φuv rt =
      rt + (StrothTypeIndex.t200 m).action.φt ruv) :
    ∃ d : Torus (StrothTypeIndex.t200 m).k,
      (StrothTypeIndex.t200 m).action.φu ruv = ruv - d + (StrothTypeIndex.t200 m).action.φuv d ∧
        (StrothTypeIndex.t200 m).action.φu (ruv + (StrothTypeIndex.t200 m).action.φuv rt) =
          rt - d + (StrothTypeIndex.t200 m).action.φt d := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt ruv
  obtain ⟨y, rfl⟩ := Torus.exists_ofInt rt
  obtain ⟨κ₁, κ₂, κ₃, e1, e2, e3⟩ := t200_cocycle_ints x y h1 h2 h3
  refine ⟨Torus.ofInt _ ![2 ^ n * (3 * κ₂ - 3 * κ₃),
      -x 0 + x 1 + 2 ^ n * (-2 * κ₁ + 2 * κ₂ - 2 * κ₃),
      x 0 - x 1 + 2 ^ n * (2 * κ₁ + 6 * κ₂ - 6 * κ₃)], ?_, ?_⟩
  · simp only [t200_φu, t200_φuv, ← Torus.ofInt_add, ← Torus.ofInt_sub]
    rw [t200_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨-2 * κ₂ + 2 * κ₃, by linear_combination⟩, ⟨0, by linear_combination -e1⟩,
      ⟨-κ₂ + κ₃, by linear_combination e1⟩⟩
  · simp only [t200_φu, t200_φuv, t200_φt, ← Torus.ofInt_add, ← Torus.ofInt_sub]
    rw [t200_ofInt_eq_iff]
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨⟨κ₁ - 5 * κ₂ + κ₃, by linear_combination e1 - e2 - e3⟩,
      ⟨-κ₂, by linear_combination -e2 - e3⟩,
      ⟨-2 * κ₂ + κ₃, by linear_combination e1 - e2 - e3⟩⟩

end Stroth34T200

end CFSG.CGT.Stroth77
