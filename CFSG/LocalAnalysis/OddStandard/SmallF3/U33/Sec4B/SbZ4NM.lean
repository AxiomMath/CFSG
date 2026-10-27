module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NH

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace ZNW4

variable (hw : ZNW4 t L S x₁ x₂ lam rho tau)
include hw

theorem F3 : ∀ e ∈ ctxE0N t tau x₁ x₂ rho, (t * e) * (t * e) = 1 →
    (∃ g : G, g * t * g⁻¹ = t * e) →
      ∃ x ∈ ctxE0N t tau x₁ x₂ rho, t * e = x * t * x⁻¹ := by
  intro e he h2 hconj
  rcases hw.mem_ctxE0N_iff.mp he with heW | ⟨w, hwW, rfl⟩
  · obtain ⟨p, hp, hp'⟩ := hw.fl_t e heW h2
    exact ⟨p, hw.mem_ctxE0N_iff.mpr (Or.inl hp), hp'⟩
  · obtain ⟨g, hg⟩ := hconj
    set x' : G := tau * w * tau⁻¹ with hx'def
    have hx'W : x' ∈ ctxWN t tau x₁ x₂ rho := hw.toCtx4Z.tau_conj_ctxWN hwW
    have htau : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hw.tau_mul_self
    have hid : (t * tau) * x' = t * (w * tau) := by
      rw [hx'def, htau]
      calc (t * tau) * (tau * w * tau)
          = t * (tau * tau) * w * tau := by group
        _ = t * w * tau := by rw [hw.tau_mul_self]; group
        _ = t * (w * tau) := by group
    have h2' : ((t * tau) * x') * ((t * tau) * x') = 1 := by
      rw [hid]; exact h2
    obtain ⟨p, hp, hp'⟩ := hw.fl_ttau x' hx'W h2'
    exfalso
    have hconj' : (p⁻¹ * g) * t * (p⁻¹ * g)⁻¹ = t * tau := by
      have h1 : (p⁻¹ * g) * t * (p⁻¹ * g)⁻¹ = p⁻¹ * (g * t * g⁻¹) * p := by group
      rw [h1, hg, ← hid, hp']
      group
    exact hw.toCtx4Z.nPre.tau_ttau_not_conj.2 (p⁻¹ * g) hconj'

section


theorem F2 : ∀ g : G, ∀ e ∈ ctxE0N t tau x₁ x₂ rho, g * t * g⁻¹ ≠ lam * e := by
  intro g e he hge
  have h2 : (lam * e) * (lam * e) = 1 := by
    rw [← hge]
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hw.t_mul_self]; group
  rcases hw.mem_ctxE0N_iff.mp he with heW | ⟨w, hwW, rfl⟩
  · obtain ⟨p, hp, hp'⟩ := hw.fl_lam e heW h2
    have hconj' : (p⁻¹ * g) * t * (p⁻¹ * g)⁻¹ = lam := by
      have h1 : (p⁻¹ * g) * t * (p⁻¹ * g)⁻¹ = p⁻¹ * (g * t * g⁻¹) * p := by group
      rw [h1, hge, hp']
      group
    exact hw.toCtx4Z.not_conj_t_lam (p⁻¹ * g) hconj'
  · set x' : G := tau * w * tau⁻¹ with hx'def
    have hx'W : x' ∈ ctxWN t tau x₁ x₂ rho := hw.toCtx4Z.tau_conj_ctxWN hwW
    have htau : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hw.tau_mul_self
    have hid : (lam * tau) * x' = lam * (w * tau) := by
      rw [hx'def, htau]
      calc (lam * tau) * (tau * w * tau)
          = lam * (tau * tau) * w * tau := by group
        _ = lam * w * tau := by rw [hw.tau_mul_self]; group
        _ = lam * (w * tau) := by group
    have h2' : ((lam * tau) * x') * ((lam * tau) * x') = 1 := by
      rw [hid]; exact h2
    obtain ⟨p, hp, hp'⟩ := hw.fl_lamtau x' hx'W h2'
    have hconj' : (p⁻¹ * g) * t * (p⁻¹ * g)⁻¹ = lam * tau := by
      have h1 : (p⁻¹ * g) * t * (p⁻¹ * g)⁻¹ = p⁻¹ * (g * t * g⁻¹) * p := by group
      rw [h1, hge, ← hid, hp']
      group
    exact hw.toCtx4Z.not_conj_t_lamtau (p⁻¹ * g) hconj'

end

end ZNW4

end CFSG.OddStandard.SmallF3.HarrisU33
