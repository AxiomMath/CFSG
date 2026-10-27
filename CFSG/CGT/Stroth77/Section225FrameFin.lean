module

public import CFSG.CGT.Stroth77.Section225FrameModTwo

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Stroth225Frame

@[expose] def devD : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 1, 0; 0, 0, 1]
@[expose] def w0a : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 0, 1; 0, 1, 0]
@[expose] def w0b : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 1, 1; 0, 0, 1]
@[expose] def w0c : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 0; 0, 1, 0; 0, 1, 1]

@[expose] def actT (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  topT * f * barT
@[expose] def actUv (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  topUv * f * barUv
@[expose] def actU (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  topU * f * barU
@[expose] def actRho (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  topRho * f * (barRho * barRho)

theorem barT_mul_self : barT * barT = 1 := by decide
theorem barUv_mul_self : barUv * barUv = 1 := by decide
theorem barU_mul_self : barU * barU = 1 := by decide
theorem barRho_cube : barRho * (barRho * barRho) = 1 := by decide

theorem eq_actT_of_mul (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : g * barT = topT * f) :
    g = actT f := by
  rw [actT, ← h, mul_assoc, barT_mul_self, mul_one]

theorem eq_actUv_of_mul (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : g * barUv = topUv * f) :
    g = actUv f := by
  rw [actUv, ← h, mul_assoc, barUv_mul_self, mul_one]

theorem eq_actU_of_mul (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : g * barU = topU * f) :
    g = actU f := by
  rw [actU, ← h, mul_assoc, barU_mul_self, mul_one]

theorem eq_actRho_of_mul (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : g * barRho = topRho * f) :
    g = actRho f := by
  rw [actRho, ← h, mul_assoc, barRho_cube, mul_one]

theorem actT_add (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) : actT (f + g) = actT f + actT g := by
  simp [actT, mul_add, add_mul]

theorem actUv_add (f g : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    actUv (f + g) = actUv f + actUv g := by
  simp [actUv, mul_add, add_mul]

theorem actT_actT (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : actT (actT f) = f := by
  have h1 : topT * topT = 1 := by decide
  simp only [actT]
  rw [show topT * (topT * f * barT) * barT = (topT * topT) * f * (barT * barT) by
    simp only [Matrix.mul_assoc], h1, barT_mul_self, Matrix.one_mul, Matrix.mul_one]

theorem actUv_actUv (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : actUv (actUv f) = f := by
  have h1 : topUv * topUv = 1 := by decide
  simp only [actUv]
  rw [show topUv * (topUv * f * barUv) * barUv = (topUv * topUv) * f * (barUv * barUv) by
    simp only [Matrix.mul_assoc], h1, barUv_mul_self, Matrix.one_mul, Matrix.mul_one]

theorem actT_actUv (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) : actT (actUv f) = actUv (actT f) := by
  have h1 : topT * topUv = topUv * topT := by decide
  have h2 : barUv * barT = barT * barUv := by decide
  simp only [actT, actUv]
  rw [show topT * (topUv * f * barUv) * barT = (topT * topUv) * f * (barUv * barT) by
      simp only [Matrix.mul_assoc],
    show topUv * (topT * f * barT) * barUv = (topUv * topT) * f * (barT * barUv) by
      simp only [Matrix.mul_assoc], h1, h2]

theorem block_of_fixed (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) (ht : actT f = f)
    (huv : actUv f = f) : f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0 ∧ f 1 0 = 0 ∧ f 2 0 = 0 := by
  have key : ∀ a b c d e g h i j : ZMod 2,
      actT !![a, b, c; d, e, g; h, i, j] = !![a, b, c; d, e, g; h, i, j] →
      actUv !![a, b, c; d, e, g; h, i, j] = !![a, b, c; d, e, g; h, i, j] →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ h = 0 := by
    decide
  rw [Matrix.eta_fin_three f] at ht huv
  exact key _ _ _ _ _ _ _ _ _ ht huv

theorem fixed_of_block (f : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hb : f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0 ∧ f 1 0 = 0 ∧ f 2 0 = 0) :
    actT f = f ∧ actUv f = f := by
  have key : ∀ e g i j : ZMod 2,
      actT !![0, 0, 0; 0, e, g; 0, i, j] = !![0, 0, 0; 0, e, g; 0, i, j] ∧
      actUv !![0, 0, 0; 0, e, g; 0, i, j] = !![0, 0, 0; 0, e, g; 0, i, j] := by
    decide
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  rw [Matrix.eta_fin_three f, h1, h2, h3, h4, h5]
  exact key _ _ _ _

theorem fixed_vec_of_uv_t (v : Fin 3 → ZMod 2) (ht : barT *ᵥ v = v) (huv : barUv *ᵥ v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  have key : ∀ a b c : ZMod 2, barT *ᵥ ![a, b, c] = ![a, b, c] →
      barUv *ᵥ ![a, b, c] = ![a, b, c] → b = 0 ∧ c = 0 := by
    decide
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at ht huv
  exact key _ _ _ ht huv

theorem block_cases (f : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hb : f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0 ∧ f 1 0 = 0 ∧ f 2 0 = 0) (hf : f ≠ 0) :
    f = devD ∨ f + actU f = devD ∨
      (f + actRho f = w0a ∨ f + actRho f = w0b ∨ f + actRho f = w0c) := by
  have key : ∀ e g i j : ZMod 2, !![0, 0, 0; 0, e, g; 0, i, j] ≠ 0 →
      !![0, 0, 0; 0, e, g; 0, i, j] = devD ∨
      !![0, 0, 0; 0, e, g; 0, i, j] + actU !![0, 0, 0; 0, e, g; 0, i, j] = devD ∨
      (!![0, 0, 0; 0, e, g; 0, i, j] + actRho !![0, 0, 0; 0, e, g; 0, i, j] = w0a ∨
        !![0, 0, 0; 0, e, g; 0, i, j] + actRho !![0, 0, 0; 0, e, g; 0, i, j] = w0b ∨
        !![0, 0, 0; 0, e, g; 0, i, j] + actRho !![0, 0, 0; 0, e, g; 0, i, j] = w0c) := by
    decide
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  rw [Matrix.eta_fin_three f, h1, h2, h3, h4, h5] at hf ⊢
  exact key _ _ _ _ hf

theorem rho_w0 (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hw : w = w0a ∨ w = w0b ∨ w = w0c) :
    (actRho w = w0a ∨ actRho w = w0b ∨ actRho w = w0c) ∧ actRho w ≠ w ∧
      (w + actRho w = w0a ∨ w + actRho w = w0b ∨ w + actRho w = w0c) := by
  rcases hw with rfl | rfl | rfl <;> decide

theorem w0_block (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hw : w = w0a ∨ w = w0b ∨ w = w0c) :
    w ≠ 0 ∧ w ≠ devD ∧ w 0 0 = 0 ∧ w 0 1 = 0 ∧ w 0 2 = 0 ∧ w 1 0 = 0 ∧ w 2 0 = 0 := by
  rcases hw with rfl | rfl | rfl <;> decide

theorem devD_block : devD ≠ 0 ∧ devD 0 0 = 0 ∧ devD 0 1 = 0 ∧ devD 0 2 = 0 ∧ devD 1 0 = 0 ∧
    devD 2 0 = 0 := by
  decide

theorem hc_cases (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hc : f 0 0 = 0 ∧ f 1 0 = 0 ∧ f 2 0 = 0)
    (hnf : ¬(actT f = f ∧ actUv f = f)) :
    (actT (f + actT f) = f + actT f ∧ actUv (f + actT f) = f + actT f ∧ f + actT f ≠ 0 ∧
        f + actT f ≠ devD) ∨
      (actT (f + actUv f) = f + actUv f ∧ actUv (f + actUv f) = f + actUv f ∧
        f + actUv f ≠ 0 ∧ f + actUv f ≠ devD) ∨
      (actT (f + actUv (actT f)) = f + actUv (actT f) ∧
        actUv (f + actUv (actT f)) = f + actUv (actT f) ∧ f + actUv (actT f) ≠ 0 ∧
        f + actUv (actT f) ≠ devD) := by
  have key : ∀ b c e g i j : ZMod 2,
      ¬(actT !![0, b, c; 0, e, g; 0, i, j] = !![0, b, c; 0, e, g; 0, i, j] ∧
        actUv !![0, b, c; 0, e, g; 0, i, j] = !![0, b, c; 0, e, g; 0, i, j]) →
      (actT (!![0, b, c; 0, e, g; 0, i, j] + actT !![0, b, c; 0, e, g; 0, i, j]) =
          !![0, b, c; 0, e, g; 0, i, j] + actT !![0, b, c; 0, e, g; 0, i, j] ∧
        actUv (!![0, b, c; 0, e, g; 0, i, j] + actT !![0, b, c; 0, e, g; 0, i, j]) =
          !![0, b, c; 0, e, g; 0, i, j] + actT !![0, b, c; 0, e, g; 0, i, j] ∧
        !![0, b, c; 0, e, g; 0, i, j] + actT !![0, b, c; 0, e, g; 0, i, j] ≠ 0 ∧
        !![0, b, c; 0, e, g; 0, i, j] + actT !![0, b, c; 0, e, g; 0, i, j] ≠ devD) ∨
      (actT (!![0, b, c; 0, e, g; 0, i, j] + actUv !![0, b, c; 0, e, g; 0, i, j]) =
          !![0, b, c; 0, e, g; 0, i, j] + actUv !![0, b, c; 0, e, g; 0, i, j] ∧
        actUv (!![0, b, c; 0, e, g; 0, i, j] + actUv !![0, b, c; 0, e, g; 0, i, j]) =
          !![0, b, c; 0, e, g; 0, i, j] + actUv !![0, b, c; 0, e, g; 0, i, j] ∧
        !![0, b, c; 0, e, g; 0, i, j] + actUv !![0, b, c; 0, e, g; 0, i, j] ≠ 0 ∧
        !![0, b, c; 0, e, g; 0, i, j] + actUv !![0, b, c; 0, e, g; 0, i, j] ≠ devD) ∨
      (actT (!![0, b, c; 0, e, g; 0, i, j] + actUv (actT !![0, b, c; 0, e, g; 0, i, j])) =
          !![0, b, c; 0, e, g; 0, i, j] + actUv (actT !![0, b, c; 0, e, g; 0, i, j]) ∧
        actUv (!![0, b, c; 0, e, g; 0, i, j] + actUv (actT !![0, b, c; 0, e, g; 0, i, j])) =
          !![0, b, c; 0, e, g; 0, i, j] + actUv (actT !![0, b, c; 0, e, g; 0, i, j]) ∧
        !![0, b, c; 0, e, g; 0, i, j] + actUv (actT !![0, b, c; 0, e, g; 0, i, j]) ≠ 0 ∧
        !![0, b, c; 0, e, g; 0, i, j] + actUv (actT !![0, b, c; 0, e, g; 0, i, j]) ≠ devD) := by
    decide
  obtain ⟨h1, h2, h3⟩ := hc
  rw [Matrix.eta_fin_three f, h1, h2, h3] at hnf ⊢
  exact key _ _ _ _ _ _ hnf

theorem f00_one_add (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (f + actUv f) 0 0 = 0 ∧ (f + actT f) 0 0 = 0 := by
  have key : ∀ a b c d e g h i j : ZMod 2,
      (!![a, b, c; d, e, g; h, i, j] + actUv !![a, b, c; d, e, g; h, i, j]) 0 0 = 0 ∧
      (!![a, b, c; d, e, g; h, i, j] + actT !![a, b, c; d, e, g; h, i, j]) 0 0 = 0 := by
    decide
  rw [Matrix.eta_fin_three f]
  exact key _ _ _ _ _ _ _ _ _

theorem devD_mulVec_eq_zero_iff (v : Fin 3 → ZMod 2) : devD *ᵥ v = 0 ↔ v 1 = 0 ∧ v 2 = 0 := by
  have key : ∀ a b c : ZMod 2, devD *ᵥ ![a, b, c] = 0 ↔ b = 0 ∧ c = 0 := by decide
  have hv : v = ![v 0, v 1, v 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  exact key _ _ _

theorem bar_mulVec_one_two {v : Fin 3 → ZMod 2} (h1 : v 1 = 0) (h2 : v 2 = 0) :
    ((barUv *ᵥ v) 1 = 0 ∧ (barUv *ᵥ v) 2 = 0) ∧ ((barT *ᵥ v) 1 = 0 ∧ (barT *ᵥ v) 2 = 0) := by
  have key : ∀ a : ZMod 2, ((barUv *ᵥ ![a, 0, 0]) 1 = 0 ∧ (barUv *ᵥ ![a, 0, 0]) 2 = 0) ∧
      ((barT *ᵥ ![a, 0, 0]) 1 = 0 ∧ (barT *ᵥ ![a, 0, 0]) 2 = 0) := by decide
  have hv : v = ![v 0, 0, 0] := by
    funext i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  rw [hv]
  exact key _

theorem false_of_f00_of_add_mem (f : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hf : f 0 0 = 1)
    (h1 : f + actUv f = 0 ∨ f + actUv f = devD) (h2 : f + actT f = 0 ∨ f + actT f = devD) :
    False := by
  have key : ∀ b c d e g h i j : ZMod 2,
      (!![1, b, c; d, e, g; h, i, j] + actUv !![1, b, c; d, e, g; h, i, j] = 0 ∨
        !![1, b, c; d, e, g; h, i, j] + actUv !![1, b, c; d, e, g; h, i, j] = devD) →
      (!![1, b, c; d, e, g; h, i, j] + actT !![1, b, c; d, e, g; h, i, j] = 0 ∨
        !![1, b, c; d, e, g; h, i, j] + actT !![1, b, c; d, e, g; h, i, j] = devD) → False := by
    decide
  rw [Matrix.eta_fin_three f, hf] at h1 h2
  exact key _ _ _ _ _ _ _ _ h1 h2

end Stroth225Frame

end CFSG.CGT.Stroth77
