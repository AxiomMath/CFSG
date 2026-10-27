module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5qc_core {Λ Δ : Type*} [Group Λ] [Group Δ] (f f' : Λ →* Δ)
    (hker : ∀ l : Λ, f l = 1 → f' l = 1) (P Q : Subgroup Δ) (t : Δ) (ht : t * t = 1)
    (hlift : ∀ q ∈ Q, ∃ l : Λ, f l = q ∧ f' l = q)
    (hnorm : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q)
    (hcent : ∀ c ∈ P, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = t)
    (hcomm : ∀ p ∈ P, p * t = t * p)
    {g : Λ} (hg : Odd (orderOf g)) (hgP : f g ∈ P) (hg'P : f' g ∈ P) : f' g = f g := by
  let c : Δ := (f g)⁻¹ * (f' g)
  have hcP : c ∈ P := mul_mem (inv_mem hgP) hg'P
  have hcentral : ∀ q ∈ Q, c * q = q * c := by
    intro q hq
    obtain ⟨l, hl, hl'⟩ := hlift q hq
    set q₂ : Δ := f g * q * (f g)⁻¹ with hq₂
    have hq₂Q : q₂ ∈ Q := hnorm (f g) hgP q hq
    obtain ⟨l₂, hl₂, hl₂'⟩ := hlift q₂ hq₂Q
    have hfl : f (g * l * g⁻¹) = q₂ := by
      rw [map_mul, map_mul, map_inv, hl, hq₂]
    have hf'l : f' (g * l * g⁻¹) = q₂ := by
      have h1 : f ((g * l * g⁻¹)⁻¹ * l₂) = 1 := by
        rw [map_mul, map_inv, hfl, hl₂, inv_mul_cancel]
      have h2 : f' ((g * l * g⁻¹)⁻¹ * l₂) = 1 := hker _ h1
      have h3 := h2
      rw [map_mul, map_inv, hl₂'] at h3
      exact (inv_mul_eq_one).mp h3
    have hq₂' : f' g * q * (f' g)⁻¹ = q₂ := by
      rw [← hf'l, map_mul, map_mul, map_inv, hl']
    have hcc : c * q * c⁻¹ = (f g)⁻¹ * (f' g * q * (f' g)⁻¹) * (f g) := by
      dsimp only [c]
      group
    have hcq : c * q * c⁻¹ = q := by
      rw [hcc, hq₂', hq₂]
      group
    calc c * q = c * q * c⁻¹ * c := by group
      _ = q * c := by rw [hcq]
  rcases hcent c hcP hcentral with hc1 | hct
  · exact ((inv_mul_eq_one).mp hc1).symm
  · have hp't : f' g = f g * t := by
      have : (f g)⁻¹ * (f' g) = t := hct
      calc f' g = f g * ((f g)⁻¹ * (f' g)) := by group
        _ = f g * t := by rw [this]
    have hfgm : f g ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hf'gm : f' g ^ orderOf g = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have htm : t ^ orderOf g = t := by
      rcases hg with ⟨k, hk⟩
      rw [hk, pow_succ, pow_mul, pow_two, ht, one_pow, one_mul]
    have ht1 : t = 1 := by
      have hm : f' g ^ orderOf g = t := by
        rw [hp't, Commute.mul_pow (hcomm (f g) hgP) (orderOf g), hfgm, one_mul, htm]
      rw [← hm, hf'gm]
    rw [hp't, ht1, mul_one]

end CFSG.OddStandard.SmallF3.Omega
