module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Alg

variable {R : Type*} [Ring R]

theorem sq_one_of_nil (h2 : ∀ x : R, x + x = 0) {α : R} (hα : α * α = 0) :
    (1 + α) * (1 + α) = 1 := by
  have e : (1 + α) * (1 + α) = 1 + (α + α) + α * α := by noncomm_ring
  rw [e, h2, hα]; simp

theorem aba_eq_bab (h2 : ∀ x : R, x + x = 0) {α β : R} (hα : α * α = 0) (hβ : β * β = 0)
    (h1 : α * β * α = α) (h1' : β * α * β = β) :
    (1 + α) * (1 + β) * (1 + α) = (1 + β) * (1 + α) * (1 + β) := by
  have e1 : (1 + α) * (1 + β) * (1 + α) =
      1 + (α + α) + β + α * β + β * α + α * α + α * β * α := by noncomm_ring
  have e2 : (1 + β) * (1 + α) * (1 + β) =
      1 + (β + β) + α + α * β + β * α + β * β + β * α * β := by noncomm_ring
  rw [e1, e2, h2, h2, hα, hβ, h1, h1']
  abel

theorem cube_eq_one (h2 : ∀ x : R, x + x = 0) {α β : R} (hα : α * α = 0) (hβ : β * β = 0)
    (h1 : α * β * α = α) (h1' : β * α * β = β) : ((1 + α) * (1 + β)) ^ 3 = 1 := by
  have hA := sq_one_of_nil h2 hα
  have hB := sq_one_of_nil h2 hβ
  have e := aba_eq_bab h2 hα hβ h1 h1'
  have : ((1 + α) * (1 + β)) ^ 3 =
      ((1 + α) * (1 + β) * (1 + α)) * ((1 + β) * (1 + α) * (1 + β)) := by noncomm_ring
  rw [this, ← e]
  calc (1 + α) * (1 + β) * (1 + α) * ((1 + α) * (1 + β) * (1 + α))
      = (1 + α) * (1 + β) * ((1 + α) * (1 + α)) * (1 + β) * (1 + α) := by noncomm_ring
    _ = 1 := by rw [hA]; calc (1 + α) * (1 + β) * 1 * (1 + β) * (1 + α)
          = (1 + α) * ((1 + β) * (1 + β)) * (1 + α) := by noncomm_ring
        _ = 1 := by rw [hB]; rw [mul_one]; exact hA

theorem fourth_eq_one (h2 : ∀ x : R, x + x = 0) {α β : R} (hα : α * α = 0) (hβ : β * β = 0)
    (h1 : α * β * α = 0) (h1' : β * α * β = 0) : ((1 + α) * (1 + β)) ^ 4 = 1 := by
  have hαβαβ : α * β * α * β = 0 := by rw [h1, zero_mul]
  have hβαβα : β * α * β * α = 0 := by rw [h1', zero_mul]
  have hαββα : α * β * (β * α) = 0 := by
    have : α * β * (β * α) = α * (β * β) * α := by noncomm_ring
    rw [this, hβ]; simp
  have hβααβ : β * α * (α * β) = 0 := by
    have : β * α * (α * β) = β * (α * α) * β := by noncomm_ring
    rw [this, hα]; simp
  have e2 : ((1 + α) * (1 + β)) ^ 2 = 1 + (α * β + β * α) := by
    have e : ((1 + α) * (1 + β)) ^ 2 = 1 + ((α + β + α * β) + (α + β + α * β)) +
        (α * α + α * β + α * (α * β) + β * α + β * β + β * (α * β) + α * β * α + α * β * β +
          α * β * (α * β)) := by noncomm_ring
    have e3 : α * (α * β) = (α * α) * β := by noncomm_ring
    have e4 : β * (α * β) = β * α * β := by noncomm_ring
    have e5 : α * β * β = α * (β * β) := by noncomm_ring
    have e6 : α * β * (α * β) = α * β * α * β := by noncomm_ring
    rw [e, h2, e3, e4, e5, e6, hα, hβ, h1, h1']
    simp only [zero_mul, mul_zero, add_zero, zero_add]
  have : ((1 + α) * (1 + β)) ^ 4 = (1 + (α * β + β * α)) * (1 + (α * β + β * α)) := by
    rw [← e2]; noncomm_ring
  rw [this]
  have e7 : (1 + (α * β + β * α)) * (1 + (α * β + β * α)) =
      1 + ((α * β + β * α) + (α * β + β * α)) +
        (α * β * (α * β) + α * β * (β * α) + β * α * (α * β) + β * α * (β * α)) := by
    noncomm_ring
  have e8 : α * β * (α * β) = α * β * α * β := by noncomm_ring
  have e9 : β * α * (β * α) = β * α * β * α := by noncomm_ring
  rw [e7, h2, e8, e9, hαβαβ, hβαβα, hαββα, hβααβ]
  simp

theorem order_cases (h2 : ∀ x : R, x + x = 0) {α β : R} (hα : α * α = 0) (hβ : β * β = 0)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hA : α * β * α = α ∨ α * β * α = 0)
    (hB : β * α * β = β ∨ β * α * β = 0) :
    ((1 + α) * (1 + β)) ^ 3 = 1 ∨ ((1 + α) * (1 + β)) ^ 4 = 1 := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact Or.inl (cube_eq_one h2 hα hβ hA hB)
  · exfalso
    have h1 : β * α = 0 := by
      have e : β * α * β * α = β * (α * β * α) := by noncomm_ring
      rw [hB, zero_mul, hA] at e
      exact e.symm
    apply hα0
    calc α = α * β * α := hA.symm
      _ = α * (β * α) := by noncomm_ring
      _ = 0 := by rw [h1, mul_zero]
  · exfalso
    have h1 : α * β = 0 := by
      have e : α * β * α * β = α * (β * α * β) := by noncomm_ring
      rw [hA, zero_mul, hB] at e
      exact e.symm
    apply hβ0
    calc β = β * α * β := hB.symm
      _ = β * (α * β) := by noncomm_ring
      _ = 0 := by rw [h1, mul_zero]
  · exact Or.inr (fourth_eq_one h2 hα hβ hA hB)

end Alg

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
