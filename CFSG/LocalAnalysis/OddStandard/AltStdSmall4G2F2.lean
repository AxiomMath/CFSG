module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Matrix

@[expose] def x2M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] def y2M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 1; 1, 1, 0]

@[expose] def y2Minv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 1, 0, 0; 1, 1, 1]

@[expose] def h1M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def h2M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

@[expose] def h2Minv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 1, 0]

@[expose] def g2M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def g3M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def g3Minv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 1, 0; 0, 0, 1]

theorem x2M_mul_x2M : x2M * x2M = 1 := by decide +kernel

theorem y2M_mul_y2Minv : y2M * y2Minv = 1 := by decide +kernel

theorem y2Minv_mul_y2M : y2Minv * y2M = 1 := by decide +kernel

theorem h1M_mul_h1M : h1M * h1M = 1 := by decide +kernel

theorem h2M_mul_h2Minv : h2M * h2Minv = 1 := by decide +kernel

theorem h2Minv_mul_h2M : h2Minv * h2M = 1 := by decide +kernel

theorem g2M_mul_g2M : g2M * g2M = 1 := by decide +kernel

theorem g3M_mul_g3Minv : g3M * g3Minv = 1 := by decide +kernel

theorem g3Minv_mul_g3M : g3Minv * g3M = 1 := by decide +kernel

@[expose] def x2G : GL (Fin 3) (ZMod 2) := ⟨x2M, x2M, x2M_mul_x2M, x2M_mul_x2M⟩

@[expose] def y2G : GL (Fin 3) (ZMod 2) := ⟨y2M, y2Minv, y2M_mul_y2Minv, y2Minv_mul_y2M⟩

@[expose] def h1G : GL (Fin 3) (ZMod 2) := ⟨h1M, h1M, h1M_mul_h1M, h1M_mul_h1M⟩

@[expose] def h2G : GL (Fin 3) (ZMod 2) := ⟨h2M, h2Minv, h2M_mul_h2Minv, h2Minv_mul_h2M⟩

@[expose] def g2G : GL (Fin 3) (ZMod 2) := ⟨g2M, g2M, g2M_mul_g2M, g2M_mul_g2M⟩

@[expose] def g3G : GL (Fin 3) (ZMod 2) := ⟨g3M, g3Minv, g3M_mul_g3Minv, g3Minv_mul_g3M⟩

@[simp] theorem val_x2G : (x2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) = x2M := rfl

@[simp] theorem val_y2G : (y2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) = y2M := rfl

@[simp] theorem val_h1G : (h1G : Matrix (Fin 3) (Fin 3) (ZMod 2)) = h1M := rfl

@[simp] theorem val_h2G : (h2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) = h2M := rfl

@[simp] theorem val_g2G : (g2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) = g2M := rfl

@[simp] theorem val_g3G : (g3G : Matrix (Fin 3) (Fin 3) (ZMod 2)) = g3M := rfl

@[simp] theorem val_inv_x2G : ((x2G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    x2M := rfl

@[simp] theorem val_inv_y2G : ((y2G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    y2Minv := rfl

@[simp] theorem val_inv_h1G : ((h1G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    h1M := rfl

@[simp] theorem val_inv_h2G : ((h2G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    h2Minv := rfl

@[simp] theorem val_inv_g2G : ((g2G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    g2M := rfl

@[simp] theorem val_inv_g3G : ((g3G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    g3Minv := rfl

theorem genRel_x2M_y2M : x2M * x2M = 1 ∧ y2M * y2M * y2M = 1 ∧ (x2M * y2M) ^ 7 = 1 ∧
    (x2M * y2M * x2M * (y2M * y2M)) ^ 4 = 1 := by
  decide +kernel

@[expose] def e1V : Fin 3 → ZMod 2 := ![1, 0, 0]

@[expose] def e2V : Fin 3 → ZMod 2 := ![0, 1, 0]

@[expose] def e3V : Fin 3 → ZMod 2 := ![0, 0, 1]

theorem h1G_mulVec_e1V : (h1G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1V = e1V := by
  decide +kernel

theorem h2G_mulVec_e1V : (h2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1V = e1V := by
  decide +kernel

theorem g2G_mulVec_e1V : (g2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1V = e2V := by
  decide +kernel

theorem g3G_mulVec_e1V : (g3G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1V = e1V + e2V := by
  decide +kernel

theorem neg_eq_self_V : ∀ v : Fin 3 → ZMod 2, -v = v := by decide +kernel

theorem eq_sum_e (v : Fin 3 → ZMod 2) : v = v 0 • e1V + v 1 • e2V + v 2 • e3V := by
  funext i
  fin_cases i <;> simp [e1V, e2V, e3V]

theorem map_eq_of_add {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (f : (Fin 3 → ZMod 2) → X) (hf : ∀ v w, f (v + w) = f v + f w) (v : Fin 3 → ZMod 2) :
    f v = v 0 • f e1V + v 1 • f e2V + v 2 • f e3V := by
  let F : (Fin 3 → ZMod 2) →+ X := AddMonoidHom.mk' f hf
  change F v = v 0 • F e1V + v 1 • F e2V + v 2 • F e3V
  conv_lhs => rw [eq_sum_e v]
  rw [map_add, map_add, ZMod.map_smul, ZMod.map_smul, ZMod.map_smul]

theorem M1 : ∀ F : Matrix (Fin 3) (Fin 3) (ZMod 2), F * x2M = x2M * F → F * y2M = y2M * F →
    F = 0 ∨ F = 1 := by
  decide +kernel

theorem M3_core : ∀ b d : Fin 3 → ZMod 2,
    x2M *ᵥ (y2M *ᵥ (x2M *ᵥ (y2M *ᵥ b))) = x2M *ᵥ (y2M *ᵥ b) + b + d →
    x2M *ᵥ (y2M *ᵥ d) = x2M *ᵥ (y2M *ᵥ b) + d → b = 0 ∧ d = 0 := by
  decide +kernel

theorem sigma_e1V : x2M *ᵥ (y2M *ᵥ e1V) = e1V + e2V := by decide +kernel

theorem sigma_e2V : x2M *ᵥ (y2M *ᵥ e2V) = e1V + e3V := by decide +kernel

theorem sigma_e3V : x2M *ᵥ (y2M *ᵥ e3V) = e2V := by decide +kernel

theorem M3_sigma (c : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → Fin 3 → ZMod 2)
    (hl : ∀ u v w, c (u + v) w = c u w + c v w) (hr : ∀ u v w, c u (v + w) = c u v + c u w)
    (ha : ∀ v, c v v = 0)
    (hσ : ∀ v w, c (((x2G * y2G : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
      (((x2G * y2G : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) =
      ((x2G * y2G : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ c v w) :
    ∀ v w, c v w = 0 := by
  have hs : ∀ v w, c (x2M *ᵥ (y2M *ᵥ v)) (x2M *ᵥ (y2M *ᵥ w)) = x2M *ᵥ (y2M *ᵥ c v w) := by
    intro v w
    have := hσ v w
    simp only [Units.val_mul, val_x2G, val_y2G, ← mulVec_mulVec] at this
    exact this
  have hswap : ∀ v w, c w v = c v w := by
    intro v w
    have h := ha (v + w)
    rw [hl, hr, hr, ha, ha, zero_add, add_zero] at h
    rw [← neg_eq_self_V (c v w), eq_neg_of_add_eq_zero_right h]
  have h12 := hs e1V e2V
  have h13 := hs e1V e3V
  have h23 := hs e2V e3V
  rw [sigma_e1V, sigma_e2V, hl, hr, hr, ha, hswap e1V e2V] at h12
  rw [sigma_e1V, sigma_e3V, hl, ha, add_zero] at h13
  rw [sigma_e2V, sigma_e3V, hl, hswap e2V e3V] at h23
  obtain ⟨h2, h3⟩ := M3_core (c e1V e3V) (c e2V e3V)
    (by rw [← h13, ← h12]; abel) (by rw [← h13, ← h23])
  have h1 : c e1V e2V = 0 := by rw [h13, h2, mulVec_zero, mulVec_zero]
  have hv1 : ∀ w, c e1V w = 0 := fun w => by
    rw [map_eq_of_add (c e1V) (hr e1V) w, ha, h1, h2, smul_zero, smul_zero, smul_zero, add_zero,
      add_zero]
  have hv2 : ∀ w, c e2V w = 0 := fun w => by
    rw [map_eq_of_add (c e2V) (hr e2V) w, hswap e1V e2V, h1, ha, h3, smul_zero, smul_zero,
      smul_zero, add_zero, add_zero]
  have hv3 : ∀ w, c e3V w = 0 := fun w => by
    rw [map_eq_of_add (c e3V) (hr e3V) w, hswap e1V e3V, h2, hswap e2V e3V, h3, ha, smul_zero,
      smul_zero, smul_zero, add_zero, add_zero]
  intro v w
  have hexp := map_eq_of_add (fun x => c x w) (fun x y => hl x y w) v
  simp only [hv1, hv2, hv3, smul_zero, add_zero] at hexp
  exact hexp

theorem M3 (c : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → Fin 3 → ZMod 2)
    (hl : ∀ u v w, c (u + v) w = c u w + c v w) (hr : ∀ u v w, c u (v + w) = c u v + c u w)
    (ha : ∀ v, c v v = 0)
    (hx : ∀ v w, c ((x2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
      ((x2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) =
      (x2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ c v w)
    (hy : ∀ v w, c ((y2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
      ((y2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) =
      (y2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ c v w) :
    ∀ v w, c v w = 0 := by
  refine M3_sigma c hl hr ha fun v w => ?_
  simp only [Units.val_mul, ← mulVec_mulVec]
  rw [hx, hy]

theorem orbit_x2y2 : ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 →
    ∃ i : Fin 7, (x2M * y2M) ^ (i : ℕ) *ᵥ v = w := by
  decide +kernel

theorem IRR (S : Set (Fin 3 → ZMod 2))
    (hx : ∀ v ∈ S, (x2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ∈ S)
    (hy : ∀ v ∈ S, (y2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ∈ S) :
    (∀ v ∈ S, v = 0) ∨ ∀ v, v ≠ 0 → v ∈ S := by
  by_cases h : ∀ v ∈ S, v = 0
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨v, hv, hv0⟩ := h
    intro w hw
    obtain ⟨i, hi⟩ := orbit_x2y2 v w hv0 hw
    rw [← hi]
    have key : ∀ m : ℕ, (x2M * y2M) ^ m *ᵥ v ∈ S := by
      intro m
      induction m with
      | zero => simpa using hv
      | succ m ih =>
        rw [pow_succ', ← mulVec_mulVec, ← mulVec_mulVec]
        exact hx _ (hy _ ih)
    exact key i

theorem IRR_of_zero_mem (S : Set (Fin 3 → ZMod 2)) (h0 : (0 : Fin 3 → ZMod 2) ∈ S)
    (hx : ∀ v ∈ S, (x2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ∈ S)
    (hy : ∀ v ∈ S, (y2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ∈ S) :
    (∀ v ∈ S, v = 0) ∨ ∀ v, v ∈ S := by
  rcases IRR S hx hy with h | h
  · exact Or.inl h
  · refine Or.inr fun v => ?_
    by_cases hv : v = 0
    · rw [hv]; exact h0
    · exact h v hv

theorem exists_mul_e1 {v : Fin 3 → ZMod 2} (hv : v ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1V = v := by
  obtain ⟨i, hi⟩ := orbit_x2y2 e1V v (by decide +kernel) hv
  refine ⟨(x2G * y2G) ^ (i : ℕ), ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mul, val_x2G, val_y2G, hi]

theorem STAB : ∀ Y : Matrix (Fin 3) (Fin 3) (ZMod 2),
    ((h1G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Y *
        ((h1G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Y = 0 ∨
      (h1G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Y *
        ((h1G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Y = 1) →
    ((h2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Y *
        ((h2G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Y = 0 ∨
      (h2G : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Y *
        ((h2G⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Y = 1) →
    Y = 0 ∨ Y = 1 := by
  decide +kernel

theorem EXP4 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M ^ 8 = 1 → M ^ 4 = 1 := by
  decide +kernel

theorem EXP4_GL (g : GL (Fin 3) (ZMod 2)) (h : g ^ 8 = 1) : g ^ 4 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  refine EXP4 _ ?_
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

end CFSG.OddStandard.AltStdSmall4.G2
