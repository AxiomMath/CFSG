module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

section Small

variable {G G' : Type} [Group G] [Group G']

theorem isCyclic_of_small (θ : G →* G') (σ₀ : G') (ζ : G) (hσ₀ : σ₀ * σ₀ = 1) (hζ2 : ζ * ζ = 1)
    (hζ1 : ζ ≠ 1) (H : Subgroup G) (hθ : ∀ β ∈ H, θ β = 1 ∨ θ β = σ₀)
    (h1 : ∀ β ∈ H, θ β = 1 → β = 1 ∨ β = ζ) (h2 : ∀ β ∈ H, θ β ≠ 1 → β * β = ζ) :
    IsCyclic ↥H ∧ Nat.card ↥H ∣ 4 ∧ ∀ β ∈ H, β * β = 1 → β ≠ 1 → β = ζ := by
  have hinv : ∀ β ∈ H, β * β = 1 → β ≠ 1 → β = ζ := by
    intro β hβ hsq hne
    by_cases hθβ : θ β = 1
    · rcases h1 β hβ hθβ with h' | h'
      · exact absurd h' hne
      · exact h'
    · have h2' := h2 β hβ hθβ
      rw [hsq] at h2'
      exact absurd h2'.symm hζ1
  by_cases hcase : ∃ κ ∈ H, θ κ ≠ 1
  · obtain ⟨κ, hκH, hθκ⟩ := hcase
    have hθκ_eq : θ κ = σ₀ := by
      rcases hθ κ hκH with h | h
      · exact absurd h hθκ
      · exact h
    have hκ2 : κ * κ = ζ := h2 κ hκH hθκ
    have hζmem : ζ ∈ Subgroup.zpowers κ := by
      rw [← hκ2]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers κ) (Subgroup.mem_zpowers κ)
    have hH_eq : H = Subgroup.zpowers κ := by
      apply le_antisymm
      · intro β hβ
        rcases hθ β hβ with h | h
        · rcases h1 β hβ h with h' | h'
          · rw [h']; exact Subgroup.one_mem _
          · rw [h']; exact hζmem
        · have hbκH : β * κ⁻¹ ∈ H := H.mul_mem hβ (H.inv_mem hκH)
          have hθbk : θ (β * κ⁻¹) = 1 := by
            rw [map_mul, map_inv, h, hθκ_eq, mul_inv_cancel]
          rcases h1 (β * κ⁻¹) hbκH hθbk with h' | h'
          · have hβκ : β = κ := mul_inv_eq_one.mp h'
            rw [hβκ]; exact Subgroup.mem_zpowers κ
          · have hβκ : β = ζ * κ := by
              calc β = (β * κ⁻¹) * κ := by group
                _ = ζ * κ := by rw [h']
            rw [hβκ]
            exact Subgroup.mul_mem _ hζmem (Subgroup.mem_zpowers κ)
      · exact Subgroup.zpowers_le.mpr hκH
    have hcyc : IsCyclic ↥H := by
      rw [hH_eq]
      exact Subgroup.isCyclic_zpowers κ
    have hcard : Nat.card ↥H ∣ 4 := by
      have hnot : ¬ κ ^ 2 ^ 1 = 1 := by
        rw [pow_one]
        intro h
        exact hζ1 (by rw [← hκ2, ← pow_two]; exact h)
      have hfin : κ ^ 2 ^ (1 + 1) = 1 := by
        rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
        calc κ ^ 4 = (κ * κ) * (κ * κ) := by
              rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two, pow_two]
          _ = ζ * ζ := by rw [hκ2]
          _ = 1 := hζ2
      have hord : orderOf κ = 4 := by
        have := orderOf_eq_prime_pow (x := κ) (n := 1) (p := 2) hnot hfin
        simpa using this
      rw [hH_eq, Nat.card_zpowers, hord]
    exact ⟨hcyc, hcard, hinv⟩
  · have hall : ∀ β ∈ H, θ β = 1 := by
      intro β hβ
      rcases hθ β hβ with h | h
      · exact h
      · by_cases hσ : σ₀ = 1
        · rw [h, hσ]
        · exfalso
          exact hcase ⟨β, hβ, by rw [h]; exact hσ⟩
    have hle : H ≤ Subgroup.zpowers ζ := by
      intro β hβ
      rcases h1 β hβ (hall β hβ) with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers ζ
    have hcyc : IsCyclic ↥H := Subgroup.isCyclic_of_le hle
    have hcard : Nat.card ↥H ∣ 4 := by
      have hdvd : Nat.card ↥H ∣ Nat.card ↥(Subgroup.zpowers ζ) := Subgroup.card_dvd_of_le hle
      rw [Nat.card_zpowers] at hdvd
      have h2' : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hζ2)
      exact dvd_trans hdvd (dvd_trans h2' (by norm_num))
    exact ⟨hcyc, hcard, hinv⟩

end Small

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
