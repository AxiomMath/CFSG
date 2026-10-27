module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_rho_mem_M (hc : Ctx4C t L S x₁ x₂ lam rho tau) : rho ∈ ctxM t tau x₁ x₂ := by
  rw [hc.M_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem w4q_conj_t_V
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {m : G}
    (hm : m ∈ ctxM t tau x₁ x₂) : ∃ u ∈ fourGrp x₁ x₂, m⁻¹ * t * m = t * u := by
  have hw := w4q_toW4Ctxc hc
  obtain ⟨u, hu, hue⟩ :=
    Set.mem_smul_set.mp (w4_conj_t_mem hw.toW4Ctx0 (inv_mem hm))
  simp only [smul_eq_mul, inv_inv] at hue
  exact ⟨u, hu, hue.symm⟩

theorem w4q_conj_tau_V
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {m : G}
    (hm : m ∈ ctxM t tau x₁ x₂) : ∃ u ∈ fourGrp x₁ x₂, m⁻¹ * tau * m = tau * u := by
  have hw := w4q_toW4Ctxc hc
  obtain ⟨u, hu, hue⟩ := Set.mem_smul_set.mp (w4_conj_tau_mem hw (inv_mem hm))
  simp only [smul_eq_mul, inv_inv] at hue
  exact ⟨u, hu, hue.symm⟩

theorem w4q_conj_comm (hc : Ctx4C t L S x₁ x₂ lam rho tau) {m l x u : G}
    (hl : l ∈ ctxO t tau x₁ x₂) (hu : u ∈ fourGrp x₁ x₂) (hmu : m⁻¹ * x * m = x * u) :
    (m * l * m⁻¹) * x * (m * l * m⁻¹)⁻¹ * x⁻¹ = m * (l * x * l⁻¹ * x⁻¹) * m⁻¹ := by
  have hlu : l * u * l⁻¹ = u := w4q_V_central hc hl hu
  have hx : x = m * (x * u) * m⁻¹ := by rw [← hmu]; group
  have h1 : l * (x * u) * l⁻¹ * (x * u)⁻¹ = l * x * l⁻¹ * x⁻¹ := by
    calc l * (x * u) * l⁻¹ * (x * u)⁻¹
        = (l * x * l⁻¹) * (l * u * l⁻¹) * u⁻¹ * x⁻¹ := by group
      _ = (l * x * l⁻¹) * u * u⁻¹ * x⁻¹ := by rw [hlu]
      _ = l * x * l⁻¹ * x⁻¹ := by group
  calc (m * l * m⁻¹) * x * (m * l * m⁻¹)⁻¹ * x⁻¹
      = m * l * (m⁻¹ * x * m) * l⁻¹ * m⁻¹ * x⁻¹ := by group
    _ = m * l * (x * u) * l⁻¹ * m⁻¹ * x⁻¹ := by rw [hmu]
    _ = m * l * (x * u) * l⁻¹ * m⁻¹ * (m * (x * u) * m⁻¹)⁻¹ := by rw [← hx]
    _ = m * (l * (x * u) * l⁻¹ * (x * u)⁻¹) * m⁻¹ := by group
    _ = m * (l * x * l⁻¹ * x⁻¹) * m⁻¹ := by rw [h1]

private theorem w4q_aux_sq (k l₀ w : G) (hk2 : k * k = 1)
    (hw : w = l₀ * k * l₀⁻¹ * k⁻¹) (hkw : k * w = w * k)
    (hcomm : (l₀ * l₀) * w = w * (l₀ * l₀)) : (k * l₀) * (k * l₀) = (l₀ * l₀) * w := by
  calc (k * l₀) * (k * l₀) = k * (l₀ * k * l₀⁻¹ * k⁻¹) * k * l₀ * l₀ := by group
    _ = k * w * k * l₀ * l₀ := by rw [← hw]
    _ = w * k * k * l₀ * l₀ := by rw [hkw]
    _ = w * (k * k) * l₀ * l₀ := by group
    _ = w * (l₀ * l₀) := by rw [hk2]; group
    _ = (l₀ * l₀) * w := hcomm.symm

theorem w4q_mem_X_of_psi_eq
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {l l₀ : G}
    (hl : l ∈ ctxO t tau x₁ x₂) (hl₀ : l₀ ∈ ctxO t tau x₁ x₂)
    (h1 : l * t * l⁻¹ * t⁻¹ = l₀ * t * l₀⁻¹ * t⁻¹)
    (h2 : l * tau * l⁻¹ * tau⁻¹ = l₀ * tau * l₀⁻¹ * tau⁻¹) :
    l * l₀⁻¹ ∈ ctxX t tau x₁ x₂ := by
  obtain ⟨φ, hφ1, hφ2, hker⟩ := w4q_exists_psi hc
  have heq : φ ⟨l, hl⟩ = φ ⟨l₀, hl₀⟩ := by
    apply Prod.ext
    · apply Subtype.ext
      rw [hφ1, hφ1]
      exact h1
    · apply Subtype.ext
      rw [hφ2, hφ2]
      exact h2
  have h : φ ((⟨l, hl⟩ : ↥(ctxO t tau x₁ x₂)) * ⟨l₀, hl₀⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  exact hker _ h

theorem w4q_sq_of_psi_eq
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {l l₀ : G}
    (hl : l ∈ ctxO t tau x₁ x₂) (hl₀ : l₀ ∈ ctxO t tau x₁ x₂)
    (h1 : l * t * l⁻¹ * t⁻¹ = l₀ * t * l₀⁻¹ * t⁻¹)
    (h2 : l * tau * l⁻¹ * tau⁻¹ = l₀ * tau * l₀⁻¹ * tau⁻¹) :
    ∃ w ∈ fourGrp x₁ x₂, l * l = l₀ * l₀ * w := by
  have hk : l * l₀⁻¹ ∈ ctxX t tau x₁ x₂ := w4q_mem_X_of_psi_eq hc hl hl₀ h1 h2
  have hkO : l * l₀⁻¹ ∈ ctxO t tau x₁ x₂ := mul_mem hl (inv_mem hl₀)
  have hk2 : (l * l₀⁻¹) * (l * l₀⁻¹) = 1 := (w4q_X_facts hc).1.mul_self_eq_one hk
  have hw : l₀ * (l * l₀⁻¹) * l₀⁻¹ * (l * l₀⁻¹)⁻¹ ∈ fourGrp x₁ x₂ := w4q_O_comm_X hc hl₀ hk
  refine ⟨_, hw, ?_⟩
  have hkw : (l * l₀⁻¹) * (l₀ * (l * l₀⁻¹) * l₀⁻¹ * (l * l₀⁻¹)⁻¹) =
      (l₀ * (l * l₀⁻¹) * l₀⁻¹ * (l * l₀⁻¹)⁻¹) * (l * l₀⁻¹) :=
    w4q_V_comm_O hc hkO hw
  have hcomm : (l₀ * l₀) * (l₀ * (l * l₀⁻¹) * l₀⁻¹ * (l * l₀⁻¹)⁻¹) =
      (l₀ * (l * l₀⁻¹) * l₀⁻¹ * (l * l₀⁻¹)⁻¹) * (l₀ * l₀) :=
    w4q_V_comm_O hc (mul_mem hl₀ hl₀) hw
  have h := w4q_aux_sq (l * l₀⁻¹) l₀ _ hk2 rfl hkw hcomm
  calc l * l = (l * l₀⁻¹ * l₀) * (l * l₀⁻¹ * l₀) := by group
    _ = _ := h

theorem w4q_conj_sq
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {m l₀ : G}
    (hm : m ∈ ctxM t tau x₁ x₂) (hl₀ : l₀ ∈ ctxO t tau x₁ x₂) :
    ∃ w ∈ fourGrp x₁ x₂, (m * l₀ * m⁻¹) * (m * l₀ * m⁻¹) = l₀ * l₀ * w := by
  have hsq : l₀ * l₀ ∈ ctxX t tau x₁ x₂ := by
    simpa [pow_two] using hc.O_quot.1 l₀ hl₀
  have hw := w4q_M_comm_X hc hm hsq
  refine ⟨_, hw, ?_⟩
  have hcomm := w4q_V_comm_O hc (mul_mem hl₀ hl₀) hw
  calc (m * l₀ * m⁻¹) * (m * l₀ * m⁻¹) = m * (l₀ * l₀) * m⁻¹ := by group
    _ = (m * (l₀ * l₀) * m⁻¹ * (l₀ * l₀)⁻¹) * (l₀ * l₀) := by group
    _ = (l₀ * l₀) * (m * (l₀ * l₀) * m⁻¹ * (l₀ * l₀)⁻¹) := hcomm.symm

theorem w4q_sq_const_conj
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {m l l₀ : G}
    (hm : m ∈ ctxM t tau x₁ x₂) (hl : l ∈ ctxO t tau x₁ x₂) (hl₀ : l₀ ∈ ctxO t tau x₁ x₂)
    (hlτ : l * tau = tau * l) (hl₀τ : l₀ * tau = tau * l₀)
    (hc₁ : l * t * l⁻¹ * t⁻¹ = m * (l₀ * t * l₀⁻¹ * t⁻¹) * m⁻¹) :
    ∃ w ∈ fourGrp x₁ x₂, l * l = l₀ * l₀ * w := by
  have hl₁ : m * l₀ * m⁻¹ ∈ ctxO t tau x₁ x₂ := (p0_normal_O t tau x₁ x₂).2 m hm l₀ hl₀
  obtain ⟨u, hu, hmu⟩ := w4q_conj_t_V hc hm
  obtain ⟨u', hu', hmu'⟩ := w4q_conj_tau_V hc hm
  have hτ1 : l * tau * l⁻¹ * tau⁻¹ = 1 := by rw [hlτ]; group
  have hτ0 : l₀ * tau * l₀⁻¹ * tau⁻¹ = 1 := by rw [hl₀τ]; group
  have e1 := w4q_conj_comm hc hl₀ hu hmu
  have e2 := w4q_conj_comm hc hl₀ hu' hmu'
  rw [hτ0] at e2
  obtain ⟨w₁, hw₁, hsq₁⟩ := w4q_sq_of_psi_eq hc hl hl₁ (by rw [hc₁, e1])
    (by rw [hτ1, e2]; group)
  obtain ⟨w₂, hw₂, hsq₂⟩ := w4q_conj_sq hc hm hl₀
  refine ⟨w₂ * w₁, mul_mem hw₂ hw₁, ?_⟩
  rw [hsq₁, hsq₂, mul_assoc]

theorem w4q_sq_const
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {l l₀ : G}
    (hl : l ∈ ctxO t tau x₁ x₂) (hl₀ : l₀ ∈ ctxO t tau x₁ x₂)
    (hlτ : l * tau = tau * l) (hl₀τ : l₀ * tau = tau * l₀)
    (hlt : l * t * l⁻¹ * t⁻¹ ≠ 1) (hl₀t : l₀ * t * l₀⁻¹ * t⁻¹ ≠ 1) :
    ∃ w ∈ fourGrp x₁ x₂, l * l = l₀ * l₀ * w := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hcV : l * t * l⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ := w4q_O_comm_X hc hl htX
  have hc₀V : l₀ * t * l₀⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂ := w4q_O_comm_X hc hl₀ htX
  have hρM := w4q_rho_mem_M hc
  rcases p0_rho_orbit_V hc4 hc₀V hl₀t hcV hlt with h | h | h
  · refine w4q_sq_const_conj hc (m := 1) (one_mem _) hl hl₀ hlτ hl₀τ ?_
    rw [h]
    group
  · exact w4q_sq_const_conj hc hρM hl hl₀ hlτ hl₀τ h
  · refine w4q_sq_const_conj hc (m := rho⁻¹) (inv_mem hρM) hl hl₀ hlτ hl₀τ ?_
    rw [inv_inv]
    exact h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
