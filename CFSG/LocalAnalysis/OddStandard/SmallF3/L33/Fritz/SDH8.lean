module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Model

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SD

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.HSFLit

theorem k8_comm_of_mem_R8 {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) : k8 * σ = σ * k8 := by
  obtain ⟨u, c, hu, rfl⟩ := hσ
  rw [aff8_mul, aff8_mul, mul_comm u5 u]
  congr 1
  rcases hu with rfl | rfl <;> revert c <;> decide

theorem comm_mem_R8 {σ τ : Perm (ZMod 8)} (hσ : σ ∈ R8) (hτ : τ ∈ R8) :
    σ * τ * σ⁻¹ * τ⁻¹ = 1 ∨ σ * τ * σ⁻¹ * τ⁻¹ = z8 := by
  obtain ⟨u, c, hu, rfl⟩ := hσ
  obtain ⟨u', c', hu', rfl⟩ := hτ
  rw [aff8_inv, aff8_inv, aff8_mul, aff8_mul, aff8_mul, ← aff8_one]
  rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;> revert c c' <;> decide

theorem z8_comm_aff8' (u : (ZMod 8)ˣ) (b : ZMod 8) : aff8 u b * z8 = z8 * aff8 u b := by
  rw [aff8_mul, aff8_mul, mul_one, one_mul]
  congr 1
  revert u b
  decide

theorem k8_sq : k8 ^ 2 = 1 := by
  rw [pow_two, aff8_mul, ← aff8_one]
  decide

theorem k8_not_mem_R8 : k8 ∉ R8 := by decide

theorem x8_mem_R8 : x8 ∈ R8 := ⟨1, 1, Or.inl rfl, by rw [mul_one]⟩

theorem y8_mem_R8 : y8 ∈ R8 := ⟨-1, 0, Or.inr rfl, by rw [mul_zero]⟩

theorem z8_mem_R8 : z8 ∈ R8 := ⟨1, 2, Or.inl rfl, rfl⟩

theorem x8_sq : x8 ^ 2 = z8 := by rw [pow_two, aff8_mul]; rfl

theorem x8_pow_four : x8 ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, x8_sq, pow_two, aff8_mul, ← aff8_one]
  rfl

theorem z8_ne_one : z8 ≠ 1 := by decide

theorem y8_sq : y8 ^ 2 = 1 := by rw [pow_two, aff8_mul, ← aff8_one]; rfl

theorem y8_x8_y8 : y8 * x8 * y8⁻¹ = x8⁻¹ := by
  rw [aff8_inv, aff8_inv, aff8_mul, aff8_mul]
  decide

theorem conj_mem_R8 {σ ρ : Perm (ZMod 8)} (hσ : σ ∈ H8) (hρ : ρ ∈ R8) : σ * ρ * σ⁻¹ ∈ R8 := by
  obtain ⟨u, b, rfl⟩ := hσ
  obtain ⟨u', c, hu', rfl⟩ := hρ
  rw [aff8_inv, aff8_mul, aff8_mul]
  rcases hu' with rfl | rfl <;> revert u b c <;> decide

@[expose] def S16 : Subgroup (Perm (ZMod 8)) where
  carrier := {g | ∃ u b, aff8 u b = g ∧ dbit8 b = fbit8 u}
  one_mem' := ⟨1, 0, aff8_one, by decide⟩
  mul_mem' := by
    rintro _ _ ⟨u, b, rfl, h⟩ ⟨u', b', rfl, h'⟩
    refine ⟨u * u', b + u * b', (aff8_mul u u' b b').symm, ?_⟩
    obtain ⟨h1, h2⟩ := type8_mul_aux u u' b b'
    rw [h1, h2, h, h']
  inv_mem' := by
    rintro _ ⟨u, b, rfl, h⟩
    refine ⟨u⁻¹, -(u⁻¹ * b), (aff8_inv u b).symm, ?_⟩
    revert u b
    decide

instance : DecidablePred (· ∈ S16) := fun _ =>
  decidable_of_iff (∃ u b, aff8 u b = _ ∧ dbit8 b = fbit8 u) Iff.rfl

theorem S16_le_H8 : S16 ≤ H8 := by
  rintro _ ⟨u, b, rfl, -⟩
  exact aff8_mem_H8 u b

theorem R8_le_S16 : R8 ≤ S16 := by
  rintro _ ⟨u, c, hu, rfl⟩
  exact ⟨u, 2 * c, rfl, by rcases hu with rfl | rfl <;> revert c <;> decide⟩

theorem k8_not_mem_S16 : k8 ∉ S16 := by decide

theorem z8_mul_k8_not_mem_S16 : z8 * k8 ∉ S16 := by decide

end CFSG.OddStandard.SmallF3.L33.KD.SD
