module

public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel

public section

namespace CFSG.EvenSporadicStandard.HypOne

open Subgroup CFSG.EvenSmallLie

theorem forall_eq_conj_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ α : MulAut X, ∃ g, α = MulAut.conj g) : ∀ α : MulAut Y, ∃ g, α = MulAut.conj g := by
  intro α
  obtain ⟨g, hg⟩ := h ((MulAut.congr e).symm α)
  refine ⟨e g, ?_⟩
  have := congrArg (MulAut.congr e) hg
  rw [MulEquiv.apply_symm_apply] at this
  rw [this]
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem foursGroupCondition_of_reps {Y : Type*} [Group Y] (reps : List (MulAut Y))
    (hcover : ∀ φ : MulAut Y, φ * φ = 1 → (∀ m : Y, φ ≠ MulAut.conj m) →
      ∃ ρ ∈ reps, ∃ ψ : MulAut Y, φ = ψ * ρ * ψ⁻¹)
    (hwit : ∀ ρ ∈ reps, ∃ l : Y, (l * (ρ l)⁻¹) ^ 2 = 1 ∧ l * (ρ l)⁻¹ ∉ center Y) :
    FoursGroupCondition Y := by
  intro φ hφ hout
  obtain ⟨ρ, hρ, ψ, hc⟩ := hcover φ hφ hout
  obtain ⟨l, hl1, hl2⟩ := hwit ρ hρ
  refine ⟨ψ l, ?_, ?_⟩
  all_goals
    have hφl : φ (ψ l) = ψ (ρ l) := by
      rw [hc]
      simp [MulAut.mul_apply]
    have hv : ψ l * (φ (ψ l))⁻¹ = ψ (l * (ρ l)⁻¹) := by
      rw [hφl, map_mul, map_inv]
  · rw [hv, ← map_pow, hl1, map_one]
  · rw [hv]
    intro hmem
    apply hl2
    generalize l * (ρ l)⁻¹ = v at hmem ⊢
    rw [mem_center_iff] at hmem ⊢
    intro g
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hmem (ψ g)

end CFSG.EvenSporadicStandard.HypOne
