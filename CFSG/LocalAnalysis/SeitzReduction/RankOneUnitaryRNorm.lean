module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SeitzReduction.RankOne

section Norm

variable {E : Type*} [Field E] [CharP E 2] (σ : E →+* E)

omit [CharP E 2] in
theorem norm_add_eq (a b : E) :
    (a + b) * σ (a + b) = a * σ a + b * σ b + (a * σ b + σ a * b) := by
  rw [map_add]
  ring

theorem eq_mul_or_eq_mul_sigma_of_norm {μ : E} (hμ : σ μ ≠ μ)
    (φ : E →+ E) (hφ : Function.Surjective φ) (hN : ∀ a, φ a * σ (φ a) = a * σ a) :
    ∃ l : E, l * σ l = 1 ∧ ((∀ a, φ a = l * a) ∨ (∀ a, φ a = l * σ a)) := by
  have hB : ∀ a b, φ a * σ (φ b) + σ (φ a) * φ b = a * σ b + σ a * b := by
    intro a b
    have h1 := hN (a + b)
    rw [map_add, norm_add_eq, norm_add_eq, hN a, hN b] at h1
    linear_combination h1
  have hμ' : μ + σ μ ≠ 0 := by
    intro h0
    apply hμ
    have : σ μ = -μ := by linear_combination h0
    rw [this, CharTwo.neg_eq]
  have hlin : ∀ c, σ c = c → ∀ a, φ (c * a) = c * φ a := by
    intro c hc a
    by_contra hne
    set d := φ (c * a) - c * φ a with hd
    have hd0 : d ≠ 0 := sub_ne_zero.mpr hne
    have hBd : ∀ e, d * σ e + σ d * e = 0 := by
      intro e
      obtain ⟨b, rfl⟩ := hφ e
      have h1 := hB (c * a) b
      have h2 := hB a b
      rw [hd, map_sub σ, map_mul σ, hc]
      rw [map_mul σ, hc] at h1
      linear_combination h1 - c * h2
    have h3 := hBd (d * μ)
    rw [map_mul σ, show d * (σ d * σ μ) + σ d * (d * μ) = (d * σ d) * (μ + σ μ) by ring] at h3
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact hd0 h5
      · exact hd0 ((map_eq_zero σ).mp h5)
    · exact hμ' h4
  set l := φ 1 with hl
  have hl1 : l * σ l = 1 := by
    have := hN 1
    rw [map_one σ, mul_one] at this
    exact this
  have hl0 : l ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hl1
    exact zero_ne_one hl1
  have hsl0 : σ l ≠ 0 := (map_ne_zero σ).mpr hl0
  set ψ : E → E := fun a => l⁻¹ * φ a with hψ
  have hψadd : ∀ a b, ψ (a + b) = ψ a + ψ b := fun a b => by
    simp only [hψ, map_add, mul_add]
  have hψ1 : ψ 1 = 1 := by simp only [hψ, ← hl, inv_mul_cancel₀ hl0]
  have hψN : ∀ a, ψ a * σ (ψ a) = a * σ a := fun a => by
    have hsl : σ l = l⁻¹ := eq_inv_of_mul_eq_one_right hl1
    simp only [hψ, map_mul, map_inv₀, hsl, inv_inv]
    rw [← hN a]
    field_simp
  have hψT : ∀ a, ψ a + σ (ψ a) = a + σ a := fun a => by
    have h1 := hB a 1
    rw [map_one σ, mul_one, mul_one] at h1
    have h1' : φ a * σ l + σ (φ a) * l = a + σ a := h1
    have hsl : σ l = l⁻¹ := eq_inv_of_mul_eq_one_right hl1
    rw [hsl] at h1'
    simp only [hψ, map_mul, map_inv₀, hsl, inv_inv]
    rw [← h1']
    ring
  have hroot : ∀ a, ψ a = a ∨ ψ a = σ a := fun a => by
    have h1 := hψN a
    have h2 := hψT a
    have h3 : (ψ a - a) * (ψ a - σ a) = 0 := by
      have : σ (ψ a) = a + σ a - ψ a := by linear_combination h2
      rw [this] at h1
      linear_combination -h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact Or.inl (sub_eq_zero.mp h4)
    · exact Or.inr (sub_eq_zero.mp h4)
  have hφeq : ∀ a, φ a = l * ψ a := fun a => by
    simp only [hψ, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
  refine ⟨l, hl1, ?_⟩
  rcases hroot μ with hψμ | hψμ
  · left
    intro a
    rw [hφeq]
    congr 1
    rcases hroot a with h1 | h1
    · exact h1
    · by_contra hne
      have hsa : σ a ≠ a := fun h2 => hne (h1.trans h2)
      rcases hroot (a + μ) with h2 | h2
      · rw [hψadd, h1, hψμ] at h2
        exact hsa (by linear_combination h2)
      · rw [hψadd, h1, hψμ, map_add] at h2
        exact hμ (by linear_combination -h2)
  · right
    intro a
    rw [hφeq]
    congr 1
    rcases hroot a with h1 | h1
    · by_contra hne
      have hsa : σ a ≠ a := fun h2 => hne (h1.trans h2.symm)
      rcases hroot (a + μ) with h2 | h2
      · rw [hψadd, h1, hψμ] at h2
        exact hμ (by linear_combination h2)
      · rw [hψadd, h1, hψμ, map_add] at h2
        exact hsa (by linear_combination -h2)
    · exact h1

end Norm

end CFSG.SeitzReduction.RankOne
