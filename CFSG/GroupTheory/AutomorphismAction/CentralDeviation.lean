module

import Mathlib.Tactic.Group

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Ring.Parity

public section

namespace CFSG.GroupTheory.AutomorphismAction

theorem pow_apply_of_fixes_center {E : Type*} [Group E] (α : E ≃* E)
    (hcenter : ∀ z ∈ Subgroup.center E, α z = z)
    (hquot : ∀ x, α x * x⁻¹ ∈ Subgroup.center E) (k : ℕ) (x : E) :
    (α ^ k) x = (α x * x⁻¹) ^ k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hd := hquot x
    have hk : (α x * x⁻¹) ^ k ∈ Subgroup.center E := Subgroup.pow_mem _ hd k
    rw [pow_succ', MulAut.mul_apply] at *
    rw [ih, map_mul, hcenter _ hk]
    simp [pow_succ, mul_assoc]

theorem pow_eq_one_of_exponent_of_fixes_center {E : Type*} [Group E] {p : ℕ}
    (hexp : ∀ x : E, x ^ p = 1) (α : E ≃* E)
    (hcenter : ∀ z ∈ Subgroup.center E, α z = z)
    (hquot : ∀ x, α x * x⁻¹ ∈ Subgroup.center E) :
    α ^ p = 1 := by
  ext x
  rw [pow_apply_of_fixes_center α hcenter hquot, hexp]
  simp

theorem pow_eq_one_of_deviation_exponent {E : Type*} [Group E] {p : ℕ} (α : E ≃* E)
    (hcenter : ∀ z ∈ Subgroup.center E, α z = z)
    (hquot : ∀ x, α x * x⁻¹ ∈ Subgroup.center E)
    (hdev : ∀ x, (α x * x⁻¹) ^ p = 1) :
    α ^ p = 1 := by
  ext x
  rw [pow_apply_of_fixes_center α hcenter hquot, hdev]
  simp

theorem fixes_center_of_derived_eq {E : Type*} [Group E] (α : E ≃* E)
    (hquot : ∀ x, α x * x⁻¹ ∈ Subgroup.center E)
    (h : commutator E = Subgroup.center E) :
    ∀ z ∈ Subgroup.center E, α z = z := by
  have fixes_derived : ∀ g ∈ commutator E, α g = g := by
    have key : ∀ x y : E, α (x * y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ := by
      intro x y
      obtain ⟨a, ha⟩ : ∃ a, α x = a * x := ⟨α x * x⁻¹, by simp⟩
      obtain ⟨b, hb⟩ : ∃ b, α y = b * y := ⟨α y * y⁻¹, by simp⟩
      have hac : a ∈ Subgroup.center E := by
        have := hquot x
        rwa [show a = α x * x⁻¹ by rw [ha]; simp]
      have hbc : b ∈ Subgroup.center E := by
        have := hquot y
        rwa [show b = α y * y⁻¹ by rw [hb]; simp]
      simp only [map_mul, map_inv, ha, hb]
      have central_comm : ∀ c : E, c ∈ Subgroup.center E → ∀ z, z * c = c * z :=
        fun c hc z => Subgroup.mem_center_iff.mp hc z
      have hai := Subgroup.inv_mem _ hac
      have hbi := Subgroup.inv_mem _ hbc
      calc a * x * (b * y) * (a * x)⁻¹ * (b * y)⁻¹
          = a * x * (b * y) * (x⁻¹ * a⁻¹) * (y⁻¹ * b⁻¹) := by simp [mul_assoc]
        _ = a * (x * (b * y) * x⁻¹) * a⁻¹ * (y⁻¹ * b⁻¹) := by simp [mul_assoc]
        _ = a * (x * b * y * x⁻¹) * a⁻¹ * (y⁻¹ * b⁻¹) := by simp [mul_assoc]
        _ = a * (b * (x * y * x⁻¹)) * a⁻¹ * (y⁻¹ * b⁻¹) := by
            rw [central_comm b hbc x]
            simp [mul_assoc]
        _ = (a * a⁻¹) * (b * (x * y * x⁻¹)) * (y⁻¹ * b⁻¹) := by
            have ea : ∀ w, a * w * a⁻¹ = w := fun w => by
              rw [mul_assoc, central_comm a⁻¹ hai w, mul_inv_cancel_left]
            rw [ea, mul_inv_cancel, one_mul]
        _ = x * y * x⁻¹ * y⁻¹ := by
            have cancellation : ∀ w, b * w * b⁻¹ = w := fun w => by
              rw [mul_assoc, central_comm b⁻¹ hbi w, mul_inv_cancel_left]
            rw [mul_inv_cancel, one_mul, central_comm b⁻¹ hbi y⁻¹,
              ← mul_assoc, cancellation]
    intro g hg
    rw [commutator_eq_closure] at hg
    refine Subgroup.closure_induction (p := fun g _ => α g = g) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨x, y, rfl⟩
      simpa [commutatorElement_def] using key x y
    · exact map_one α
    · intro x y _ _ hx hy
      rw [map_mul, hx, hy]
    · intro x _ hx
      rw [map_inv, hx]
  exact fun z hz => fixes_derived z (h ▸ hz)

theorem eq_one_of_involutive_centralizing {E : Type*} [Group E] {p : ℕ} (hp : Odd p)
    (hexp : ∀ x : E, x ^ p = 1) (α : E ≃* E) (hinv : ∀ x, α (α x) = x)
    (hcenter : ∀ z ∈ Subgroup.center E, α z = z)
    (hquot : ∀ x, α x * x⁻¹ ∈ Subgroup.center E) :
    α = 1 := by
  ext y
  have hd := hquot y
  have h1 : α (α y * y⁻¹) = α y * y⁻¹ := hcenter _ hd
  have h2 : (α y * y⁻¹) ^ 2 = 1 := by
    have h3 : α (α y * y⁻¹) = y * α y⁻¹ := by simp [hinv]
    have h4 : y * (α y)⁻¹ = α y * y⁻¹ := by rw [← map_inv, ← h3, h1]
    have h5 : (α y * y⁻¹) * (α y * y⁻¹) = 1 := by
      calc (α y * y⁻¹) * (α y * y⁻¹) = (α y * y⁻¹) * (y * (α y)⁻¹) := by rw [h4]
        _ = 1 := by group
    simpa [pow_two] using h5
  obtain ⟨k, hk⟩ := hp
  have h6 : (α y * y⁻¹) = 1 := by
    have := hexp (α y * y⁻¹)
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at this
    exact this
  simpa [mul_inv_eq_one] using h6

end CFSG.GroupTheory.AutomorphismAction
