module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412c

public section

namespace CFSG.QuasithinUnique.Lin2

section Hilbert

variable {K : Type*} [Field K] [Finite K]

theorem exists_ne_zero_twisted (hk2 : (2 : K) = 0) (σ : K ≃+* K) (hσσ : ∀ a, σ (σ a) = a)
    (θ : K) (hθ : σ θ ≠ θ) {c : K} (hc : c * σ c = 1) (hK : 1 < Nat.card K) :
    ∃ v : K, v ≠ 0 ∧ c * σ v = v := by
  by_contra hcon
  have hall : ∀ v : K, c * σ v = v → v = 0 := fun v hv => by
    by_contra hv0
    exact hcon ⟨v, hv0, hv⟩
  have h1 := card_twisted_fixed hk2 σ hσσ θ hθ c hc
  have h2 : Nat.card {a : K // c * σ a = a} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext ((hall x.1 x.2).trans (hall y.1 y.2).symm)⟩,
      ⟨⟨0, by simp⟩⟩⟩
  rw [h2] at h1
  omega

theorem hilbert90_package (hk2 : (2 : K) = 0) (σ : K ≃+* K) (hσσ : ∀ a, σ (σ a) = a) (θ : K)
    (hθ : σ θ ≠ θ) (hK : 1 < Nat.card K) {a b c : K} (ha : a ≠ 0) (haσ : a * σ a = 1)
    (hb : σ b = b) (hc : c * σ c = 1) :
    ∃ h k l : K, h ≠ 0 ∧ l ≠ 0 ∧ σ h = h * a ∧ σ k = h * b + k * a⁻¹ ∧ σ l = c * l := by
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_twisted hk2 σ hσσ θ hθ haσ hK
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_twisted hk2 σ hσσ θ hθ hc hK
  have haa : a * a * σ (a * a) = 1 := by
    rw [map_mul]
    linear_combination (a * σ a + 1) * haσ
  obtain ⟨κ, hκ⟩ := twisted_free hk2 σ hσσ θ hθ (a * a) haa (a * b) (by
    rw [map_mul, hb]
    linear_combination a * b * haσ)
  have hσh : σ v⁻¹ = v⁻¹ * a := by
    rw [map_inv₀]
    apply inv_eq_of_mul_eq_one_right
    calc σ v * (v⁻¹ * a) = (a * σ v) * v⁻¹ := by ring
      _ = v * v⁻¹ := by rw [hv]
      _ = 1 := mul_inv_cancel₀ hv0
  have hσl : σ w⁻¹ = c * w⁻¹ := by
    rw [map_inv₀]
    apply inv_eq_of_mul_eq_one_right
    calc σ w * (c * w⁻¹) = (c * σ w) * w⁻¹ := by ring
      _ = w * w⁻¹ := by rw [hw]
      _ = 1 := mul_inv_cancel₀ hw0
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  refine ⟨v⁻¹, v⁻¹ * κ, w⁻¹, inv_ne_zero hv0, inv_ne_zero hw0, hσh, ?_, hσl⟩
  rw [map_mul, hσh]
  have h4 : a * σ κ = b + κ * a⁻¹ := by
    apply mul_left_cancel₀ ha
    linear_combination (-1) * hκ - κ * hinv - κ * hk2
  linear_combination v⁻¹ * h4

end Hilbert

end CFSG.QuasithinUnique.Lin2
