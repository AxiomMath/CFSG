module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapData

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G]

private lemma fixesSwapComm {σ : Perm (Fin 10)} {a b : Fin 10}
    (ha : σ a = a) (hb : σ b = b) : σ * swap a b = swap a b * σ := by
  rw [Equiv.mul_swap_eq_swap_mul, ha, hb]

private lemma d0CommOfFixes01 {d₀ : G} {κ₁ : Perm (Fin 10) →* G}
    (e₀ : κ₁ (swap 0 1) = d₀) {σ : Perm (Fin 10)} (h0 : σ 0 = 0) (h1 : σ 1 = 1) :
    d₀ * κ₁ σ = κ₁ σ * d₀ := by
  rw [← e₀, ← map_mul, ← map_mul, fixesSwapComm h0 h1]

private lemma memBDecomp {d₀ d₁ : G} {κ₀ : Perm (Fin 10) →* G}
    (h₀ : CentData d₀ κ₀) (e₁ : κ₀ (swap 2 3) = d₁) {b : G}
    (hb0 : b ∈ Subgroup.centralizer ({d₀} : Set G))
    (hb1 : b ∈ Subgroup.centralizer ({d₁} : Set G)) :
    ∃ (a : Fin 2) (σ : Perm (Fin 10)), b = d₀ ^ (a : ℕ) * κ₀ σ ∧
      σ * swap 2 3 = swap 2 3 * σ := by
  have hbd1 : b * d₁ = d₁ * b := Subgroup.mem_centralizer_singleton_iff.1 hb1
  obtain ⟨σ, hσ | hσ⟩ := h₀.cases b hb0
  · refine ⟨0, σ, by rw [hσ]; simp, ?_⟩
    have hκ : κ₀ σ * κ₀ (swap 2 3) = κ₀ (swap 2 3) * κ₀ σ := by
      rw [hσ, ← e₁] at hbd1
      exact hbd1
    exact h₀.inj (by rw [map_mul, map_mul]; exact hκ)
  · refine ⟨1, σ, by rw [hσ]; simp, ?_⟩
    have hdb : d₀ * b = κ₀ σ := by
      rw [hσ, ← mul_assoc, h₀.mul_self, one_mul]
    have hd0d1 : d₀ * d₁ = d₁ * d₀ := by
      rw [← e₁]; exact h₀.comm (swap 2 3)
    have hκσd1 : κ₀ σ * d₁ = d₁ * κ₀ σ := by
      rw [← hdb, mul_assoc, hbd1, ← mul_assoc, hd0d1, mul_assoc]
    have hκ : κ₀ σ * κ₀ (swap 2 3) = κ₀ (swap 2 3) * κ₀ σ := by
      rw [← e₁] at hκσd1
      exact hκσd1
    exact h₀.inj (by rw [map_mul, map_mul]; exact hκ)

private lemma conjKappa {d : G} {κ : Perm (Fin 10) →* G}
    (hd : ∀ σ, d * κ σ = κ σ * d)
    {w : G} (hw : w = 1 ∨ w = d) (σ τ : Perm (Fin 10)) :
    (κ τ) * (w * κ σ) * (κ τ)⁻¹ = w * κ (τ * σ * τ⁻¹) := by
  rcases hw with hw | hw
  · rw [hw]; simp only [one_mul]
    rw [← map_mul, ← map_inv, ← map_mul]
  · rw [hw]
    rw [show (κ τ) * (d * κ σ) * (κ τ)⁻¹ = (κ τ) * d * κ σ * (κ τ)⁻¹ by group]
    rw [← hd τ]
    rw [show (d * κ τ) * κ σ * (κ τ)⁻¹ = d * (κ τ * κ σ * (κ τ)⁻¹) by group]
    rw [← map_mul, ← map_inv, ← map_mul]

private lemma conjDecomp {d : G} {κ : Perm (Fin 10) →* G}
    (hd : ∀ σ, d * κ σ = κ σ * d) (hd2 : d * d = 1)
    {w u : G} (hw : w = 1 ∨ w = d) (hu : u = 1 ∨ u = d)
    (σ σr : Perm (Fin 10)) :
    (u * κ σr) * (w * κ σ) * (u * κ σr)⁻¹ = w * κ (σr * σ * σr⁻¹) := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_left hd2
  have key := conjKappa (d := d) (κ := κ) hd hw σ σr
  rcases hu with hu | hu
  · rw [hu]; simpa using key
  · rw [hu]
    rw [show (d * κ σr) * (w * κ σ) * (d * κ σr)⁻¹
        = d * ((κ σr) * (w * κ σ) * (κ σr)⁻¹) * d⁻¹ by group]
    rw [key]
    rcases hw with hw | hw
    · rw [hw]; simp only [one_mul]
      rw [hd (σr * σ * σr⁻¹), mul_assoc, mul_inv_cancel, mul_one]
    · rw [hw]
      rw [show d * (d * κ (σr * σ * σr⁻¹)) * d⁻¹
          = (d * d) * κ (σr * σ * σr⁻¹) * d⁻¹ by group]
      rw [hd2, one_mul, hdi, ← hd (σr * σ * σr⁻¹)]

private lemma mulDecomp {d : G} {κ : Perm (Fin 10) →* G}
    (hd : ∀ σ, d * κ σ = κ σ * d) (hd2 : d * d = 1)
    {w : G} (hw : w = 1 ∨ w = d) (σ τ : Perm (Fin 10)) :
    (w * κ σ) * (w * κ τ) = κ (σ * τ) := by
  rcases hw with hw | hw
  · rw [hw]; simp only [one_mul, ← map_mul]
  · rw [hw]
    calc (d * κ σ) * (d * κ τ)
        = d * ((κ σ * d) * κ τ) := by simp only [mul_assoc]
      _ = d * ((d * κ σ) * κ τ) := by rw [← hd σ]
      _ = (d * d) * (κ σ * κ τ) := by simp only [mul_assoc]
      _ = κ σ * κ τ := by rw [hd2, one_mul]
      _ = κ (σ * τ) := by rw [← map_mul]

theorem eq_one_of_two_frames {d₀ d₁ : G} {κ₀ κ₁ : Perm (Fin 10) →* G}
    (h₀ : CentData d₀ κ₀) (h₁ : CentData d₁ κ₁)
    (e₀ : κ₁ (swap 0 1) = d₀) (e₁ : κ₀ (swap 2 3) = d₁)
    {π₀ π₁ : Perm (Fin 10)} (hπ₀ : π₀ 2 = 2 ∧ π₀ 3 = 3)
    (hπ₁ : ∃ t₁ t₂ ρ : Perm (Fin 10), π₁ = t₁ * t₂ ∧ ρ * t₁ * ρ⁻¹ = t₂ ∧
      t₁ 0 = 0 ∧ t₁ 1 = 1 ∧ t₂ 0 = 0 ∧ t₂ 1 = 1 ∧ ρ 0 = 0 ∧ ρ 1 = 1)
    {ε₀ ε₁ : G} (hε₀ : ε₀ = 1 ∨ ε₀ = d₀) (hε₁ : ε₁ = 1 ∨ ε₁ = d₁)
    (h : ε₀ * κ₀ π₀ = ε₁ * κ₁ π₁) : ε₀ = 1 := by
  have _ := hπ₀
  obtain ⟨t₁, t₂, ρ, rfl, hρt, ht1_0, ht1_1, ht2_0, ht2_1, hρ0, hρ1⟩ := hπ₁
  have hx0 : κ₁ t₁ ∈ Subgroup.centralizer ({d₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (d0CommOfFixes01 e₀ ht1_0 ht1_1).symm
  have hx1 : κ₁ t₁ ∈ Subgroup.centralizer ({d₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (h₁.comm t₁).symm
  have hr0 : κ₁ ρ ∈ Subgroup.centralizer ({d₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (d0CommOfFixes01 e₀ hρ0 hρ1).symm
  have hr1 : κ₁ ρ ∈ Subgroup.centralizer ({d₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (h₁.comm ρ).symm
  obtain ⟨a, σ, hx, _hσc⟩ := memBDecomp h₀ e₁ hx0 hx1
  obtain ⟨a', σr, hr, _hσrc⟩ := memBDecomp h₀ e₁ hr0 hr1
  have hw : d₀ ^ (a : ℕ) = 1 ∨ d₀ ^ (a : ℕ) = d₀ := by fin_cases a <;> simp
  have hu : d₀ ^ (a' : ℕ) = 1 ∨ d₀ ^ (a' : ℕ) = d₀ := by fin_cases a' <;> simp
  have hy : κ₁ t₂ = κ₁ ρ * κ₁ t₁ * (κ₁ ρ)⁻¹ := by
    rw [← hρt, map_mul, map_mul, map_inv]
  have hconj : κ₁ ρ * κ₁ t₁ * (κ₁ ρ)⁻¹ = d₀ ^ (a : ℕ) * κ₀ (σr * σ * σr⁻¹) := by
    rw [hx, hr]
    exact conjDecomp (d := d₀) (κ := κ₀) h₀.comm h₀.mul_self hw hu σ σr
  have hy_val : κ₁ t₂ = d₀ ^ (a : ℕ) * κ₀ (σr * σ * σr⁻¹) := by
    rw [hy, hconj]
  let τ : Perm (Fin 10) := σ * (σr * σ * σr⁻¹)
  have hxy : κ₁ t₁ * κ₁ t₂ = κ₀ τ := by
    rw [hx, hy_val]
    exact mulDecomp (d := d₀) (κ := κ₀) h₀.comm h₀.mul_self hw σ (σr * σ * σr⁻¹)
  have hπ₁' : κ₁ (t₁ * t₂) = κ₀ τ := by
    rw [map_mul]
    exact hxy
  have hcontr : ∀ τ' : Perm (Fin 10), d₀ * κ₀ π₀ = κ₀ τ' → False := by
    intro τ' hτ'
    have hcalc : κ₀ (τ' * π₀⁻¹) = d₀ := by
      rw [map_mul, map_inv, ← hτ', mul_assoc, mul_inv_cancel, mul_one]
    exact h₀.ne_z _ hcalc
  rcases hε₀ with hε₀ | hε₀
  · exact hε₀
  · exfalso
    rcases hε₁ with hε₁ | hε₁
    · apply hcontr τ
      rw [hε₀, hε₁, one_mul, hπ₁'] at h
      exact h
    · apply hcontr (swap 2 3 * τ)
      rw [hε₀, hε₁, ← e₁, hπ₁', ← map_mul] at h
      exact h

end CFSG.OddStandard.AltStdSec.SwapPartner
