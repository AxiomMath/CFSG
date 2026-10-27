module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapRetract

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem isConj_ι_iff (hC : CentData z ι) {σ σ' : Perm (Fin 10)} (h : IsConj σ σ') :
    IsConj z (ι σ) ↔ IsConj z (ι σ') := by
  have hι : IsConj (ι σ) (ι σ') := ι.map_isConj h
  constructor
  · exact fun hz => hz.trans hι
  · exact fun hz => hz.trans hι.symm

theorem isConj_z_mul_ι_iff (hC : CentData z ι) {σ σ' : Perm (Fin 10)} (h : IsConj σ σ') :
    IsConj z (z * ι σ) ↔ IsConj z (z * ι σ') := by
  have hι : IsConj (z * ι σ) (z * ι σ') := by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨ι c, ?_⟩
    calc ι c * (z * ι σ) * (ι c)⁻¹
        = (ι c * z) * (ι σ * (ι c)⁻¹) := by group
      _ = (z * ι c) * (ι σ * (ι c)⁻¹) := by rw [(hC.comm c).symm]
      _ = z * (ι c * ι σ * (ι c)⁻¹) := by group
      _ = z * ι (c * σ * c⁻¹) := by rw [← map_mul, ← map_inv, ← map_mul]
      _ = z * ι σ' := by rw [hc]
  constructor
  · exact fun hz => hz.trans hι
  · exact fun hz => hz.trans hι.symm

theorem not_isConj_ι_of_sq (hC : CentData z ι) {σ : Perm (Fin 10)} (h : ∃ γ, γ * γ = σ) :
    ¬ IsConj z (ι σ) := by
  intro hz
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨g, hg⟩ := isConj_iff.1 hz.symm
  refine hC.not_sq (g * ι γ * g⁻¹) ?_
  rw [show (g * ι γ * g⁻¹) * (g * ι γ * g⁻¹) = g * (ι γ * ι γ) * g⁻¹ by group,
    ← map_mul, hγ]
  exact hg

theorem isConj_ι_of_isSwap (hC : CentData z ι) (hx : IsConj z (ι τ₀)) {σ : Perm (Fin 10)}
    (h : σ.IsSwap) : IsConj z (ι σ) := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have hσconj : IsConj (swap a b) τ₀ := by
    simpa [τ₀] using Equiv.Perm.isConj_swap hab (by decide : (8 : Fin 10) ≠ 9)
  exact (isConj_ι_iff hC hσconj).2 hx

theorem isConj_ι₁_of_isSwap {ι₁ : Perm (Fin 10) →* G} (h1 : ι₁ τ₀ = z) {σ : Perm (Fin 10)}
    (h : σ.IsSwap) : IsConj z (ι₁ σ) := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have hconj : IsConj (swap a b) τ₀ := by
    simpa [τ₀] using Equiv.Perm.isConj_swap hab (by decide : (8 : Fin 10) ≠ 9)
  have h2 : IsConj (ι₁ (swap a b)) (ι₁ τ₀) := ι₁.map_isConj hconj
  rw [h1] at h2
  exact h2.symm

theorem isConj_mul_ι₁_of_isSwap {x : G} {ι₁ : Perm (Fin 10) →* G} (hC₁ : CentData x ι₁)
    (h1 : ι₁ τ₀ = z) (hP1 : IsConj z (x * z)) {σ : Perm (Fin 10)} (h : σ.IsSwap) :
    IsConj z (x * ι₁ σ) := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have hconj : IsConj (swap a b) τ₀ := by
    simpa [τ₀] using Equiv.Perm.isConj_swap hab (by decide : (8 : Fin 10) ≠ 9)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hxz : IsConj (x * ι₁ (swap a b)) (x * z) := by
    refine isConj_iff.2 ⟨ι₁ c, ?_⟩
    calc ι₁ c * (x * ι₁ (swap a b)) * (ι₁ c)⁻¹
        = (ι₁ c * x) * (ι₁ (swap a b) * (ι₁ c)⁻¹) := by group
      _ = (x * ι₁ c) * (ι₁ (swap a b) * (ι₁ c)⁻¹) := by rw [(hC₁.comm c).symm]
      _ = x * (ι₁ c * ι₁ (swap a b) * (ι₁ c)⁻¹) := by group
      _ = x * ι₁ (c * swap a b * c⁻¹) := by rw [← map_mul, ← map_inv, ← map_mul]
      _ = x * ι₁ τ₀ := by rw [hc]
      _ = x * z := by rw [h1]
  exact hP1.trans hxz.symm


end CFSG.OddStandard.AltStdSec.SwapPartner
