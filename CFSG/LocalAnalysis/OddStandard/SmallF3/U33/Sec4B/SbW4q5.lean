module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_sq_formula (l d : G) :
    (l * d) * (l * d) = (l * d * l⁻¹ * d⁻¹) * (d * (l * l) * d⁻¹ * (l * l)⁻¹) * (l * l) *
      (d * d) := by
  group

private theorem w4q_aux_solve (P Q R : G) (h : P * R * Q = 1) : R = P⁻¹ * Q⁻¹ := by
  calc R = P⁻¹ * (P * R * Q) * Q⁻¹ := by group
    _ = P⁻¹ * Q⁻¹ := by rw [h]; group

theorem w4q_sq_decomp_mem
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {l d : G}
    (hl : l ∈ ctxO t tau x₁ x₂) (hd : d ∈ ctxO t tau x₁ x₂) (hdt : d * t = t * d)
    (hl2 : l * l ∈ ctxE t x₁ x₂) : (l * d) * (l * d) ∈ ctxE t x₁ x₂ := by
  have hVE := w4q_V_le_E t x₁ x₂
  have hl2X : l * l ∈ ctxX t tau x₁ x₂ := w4q_E_le_X t tau x₁ x₂ hl2
  have hv₂ : d * (l * l) * d⁻¹ * (l * l)⁻¹ ∈ fourGrp x₁ x₂ := w4q_O_comm_X hc hd hl2X
  rw [w4q_sq_formula]
  exact mul_mem (mul_mem (mul_mem (w4q_comm_O_D hc hl hd hdt) (hVE hv₂)) hl2)
    (hVE (w4q_sq_D hc hd hdt))

theorem w4q_sq_of_sq_one
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {l d : G}
    (hl : l ∈ ctxO t tau x₁ x₂) (hd : d ∈ ctxO t tau x₁ x₂) (hdt : d * t = t * d)
    (h : (l * d) * (l * d) = 1) : l * l ∈ ctxE t x₁ x₂ := by
  have hVE := w4q_V_le_E t x₁ x₂
  have hl2X : l * l ∈ ctxX t tau x₁ x₂ := by
    simpa [pow_two] using hc.O_quot.1 l hl
  have hv₂ : d * (l * l) * d⁻¹ * (l * l)⁻¹ ∈ fourGrp x₁ x₂ := w4q_O_comm_X hc hd hl2X
  have hform := w4q_sq_formula l d
  rw [h] at hform
  have hsolve := w4q_aux_solve _ _ _ hform.symm
  rw [hsolve]
  exact mul_mem (inv_mem (mul_mem (w4q_comm_O_D hc hl hd hdt) (hVE hv₂)))
    (inv_mem (hVE (w4q_sq_D hc hd hdt)))

theorem w4q_H_of_bad
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hbad : ∃ l₀ ∈ ctxO t tau x₁ x₂, l₀ * tau = tau * l₀ ∧ l₀ * l₀ ∉ fourGrp x₁ x₂) :
    ∀ u ∈ ctxO t tau x₁ x₂, u * u = 1 → u * t = t * u := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  obtain ⟨l₀, hl₀, hl₀τ, hl₀sq⟩ := hbad
  intro u hu hu2
  obtain ⟨l, hl, d, hd, hlτ, hdt, rfl⟩ := w4q_decomp hc hu
  have hlt : l * t * l⁻¹ * t⁻¹ = 1 := by
    by_contra hne
    have hne₀ : l₀ * t * l₀⁻¹ * t⁻¹ ≠ 1 := by
      intro h1
      apply hl₀sq
      have hτ0 : l₀ * tau * l₀⁻¹ * tau⁻¹ = 1 := by rw [hl₀τ]; group
      have hX : l₀ ∈ ctxX t tau x₁ x₂ :=
        w4_mem_X_of_mem_R hc4 (w4_O_le_R (w4q_toW4Ctxc hc).toW4Ctxb hl₀) h1 hτ0
      rw [(w4q_X_facts hc).1.mul_self_eq_one hX]
      exact one_mem _
    obtain ⟨w, hw, hsq⟩ := w4q_sq_const hc hl hl₀ hlτ hl₀τ hne hne₀
    have hl2E : l * l ∈ ctxE t x₁ x₂ := w4q_sq_of_sq_one hc hl hd hdt hu2
    have hl₀2E : l₀ * l₀ ∈ ctxE t x₁ x₂ := by
      have h1 : l₀ * l₀ = (l * l) * w⁻¹ := by rw [hsq]; group
      rw [h1]
      exact mul_mem hl2E (inv_mem (w4q_V_le_E t x₁ x₂ hw))
    rcases w4q_E_cases hc hl₀2E with h | h
    · exact hl₀sq h
    · apply w4q_not_sq_tV hc l₀ h
      calc l₀ * l₀ = (t * t) * (l₀ * l₀) := by rw [w4q_t_mul_t hc, one_mul]
        _ = t * (t * (l₀ * l₀)) := mul_assoc _ _ _
  have hltc : l * t = t * l := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hlt)
  calc l * d * t = l * (d * t) := by group
    _ = l * (t * d) := by rw [hdt]
    _ = (l * t) * d := by group
    _ = (t * l) * d := by rw [hltc]
    _ = t * (l * d) := by group

theorem w4q_sq_mem_V
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hF : (∀ u ∈ ctxO t tau x₁ x₂, u * u = 1 → u * t = t * u) → False) :
    ∀ g ∈ ctxO t tau x₁ x₂, g * g ∈ fourGrp x₁ x₂ := by
  by_cases hL : ∀ l ∈ ctxO t tau x₁ x₂, l * tau = tau * l → l * l ∈ fourGrp x₁ x₂
  · intro g hg
    obtain ⟨l, hl, d, hd, hlτ, hdt, rfl⟩ := w4q_decomp hc hg
    have hl2E : l * l ∈ ctxE t x₁ x₂ := w4q_V_le_E t x₁ x₂ (hL l hl hlτ)
    have hgE : (l * d) * (l * d) ∈ ctxE t x₁ x₂ := w4q_sq_decomp_mem hc hl hd hdt hl2E
    rcases w4q_E_cases hc hgE with h | h
    · exact h
    · exfalso
      apply w4q_not_sq_tV hc (l * d) h
      calc (l * d) * (l * d) = (t * t) * ((l * d) * (l * d)) := by rw [w4q_t_mul_t hc, one_mul]
        _ = t * (t * ((l * d) * (l * d))) := mul_assoc _ _ _
  · exfalso
    push_neg at hL
    obtain ⟨l₀, hl₀, hl₀τ, hl₀sq⟩ := hL
    exact hF (w4q_H_of_bad hc ⟨l₀, hl₀, hl₀τ, hl₀sq⟩)

theorem w4q_comm_mem_V (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hsq : ∀ g ∈ ctxO t tau x₁ x₂, g * g ∈ fourGrp x₁ x₂) {a b : G}
    (ha : a ∈ ctxO t tau x₁ x₂) (hb : b ∈ ctxO t tau x₁ x₂) :
    a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂ := by
  have h1 : (a * b) * (a * b) ∈ fourGrp x₁ x₂ := hsq _ (mul_mem ha hb)
  have h2 : (a * a)⁻¹ ∈ fourGrp x₁ x₂ := inv_mem (hsq a ha)
  have h3 : (b * b)⁻¹ ∈ fourGrp x₁ x₂ := inv_mem (hsq b hb)
  have h4 : b⁻¹ * (a * a)⁻¹ * b⁻¹⁻¹ = (a * a)⁻¹ := w4q_V_central hc (inv_mem hb) h2
  have h5 : b⁻¹ * (a * a)⁻¹ * b = (a * a)⁻¹ := by simpa using h4
  have hid : a * b * a⁻¹ * b⁻¹ =
      ((a * b) * (a * b)) * (b⁻¹ * (a * a)⁻¹ * b) * (b * b)⁻¹ := by group
  rw [hid, h5]
  exact mul_mem (mul_mem h1 h2) h3

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
