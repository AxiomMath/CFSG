module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13K0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma c13K_sq_ne_one_of_gamma (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {γ q : G}
    (hγM : γ ∈ ctxM t tau x₁ x₂) (hγsq : γ ^ 2 = tau) (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    (γ * q) ^ 2 ≠ 1 := by
  intro h1
  have hq' : γ * q * γ⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hc.normal_Q.2 γ hγM q hq
  have htauq : tau * q = q⁻¹ * tau := by
    have h := hc.tau_inv_Q q hq
    calc tau * q = (tau * q * tau⁻¹) * tau := by group
      _ = q⁻¹ * tau := by rw [h]
  have hsq : (γ * q) ^ 2 = (γ * q * γ⁻¹ * q⁻¹) * tau := by
    calc (γ * q) ^ 2 = (γ * q * γ⁻¹) * γ ^ 2 * q := by rw [pow_two]; group
      _ = (γ * q * γ⁻¹) * tau * q := by rw [hγsq]
      _ = (γ * q) * γ⁻¹ * (tau * q) := by group
      _ = (γ * q) * γ⁻¹ * (q⁻¹ * tau) := by rw [htauq]
      _ = (γ * q * γ⁻¹ * q⁻¹) * tau := by group
  have hone : (γ * q * γ⁻¹ * q⁻¹) * tau = 1 := by rw [← hsq]; exact h1
  have heq : γ * q * γ⁻¹ * q⁻¹ = tau⁻¹ := eq_inv_of_mul_eq_one_left hone
  have hmem : tau⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [← heq]
    exact (ctxQ t tau x₁ x₂ rho).mul_mem hq' ((ctxQ t tau x₁ x₂ rho).inv_mem hq)
  have htau_inv : tau⁻¹ = tau := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two]
    exact (c13K_rel hc).2.2.2.1
  rw [htau_inv] at hmem
  exact (c13K_not_mem_Q hc).2.1 hmem

theorem c13K_O_cases (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {x : G}
    (hx : x ∈ ctxO t tau x₁ x₂) :
    x ∈ ctxR t tau x₁ x₂ ∨ ∃ r ∈ ctxR t tau x₁ x₂, x = om * r := by
  have homO : om ∈ ctxO t tau x₁ x₂ := (Subgroup.mem_inf.mp hc.om_mem).1
  have homR : om ∉ ctxR t tau x₁ x₂ := by
    intro hR
    have homC : om ∈ centralizer ({rho} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (c13K_rho_comm hc).2.2.symm
    have hmem : om ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hR, homC⟩
    rw [hc.CR_rho] at hmem
    exact hc.om_not_mem hmem
  have hrel : (ctxR t tau x₁ x₂).relIndex (ctxO t tau x₁ x₂) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := ctxR t tau x₁ x₂) (K := ctxO t tau x₁ x₂)
    rw [inf_eq_left.mpr hc.R_le_O, hc.card_R, hc.card_O] at h
    norm_num at h
    omega
  have hH0 : ((ctxR t tau x₁ x₂).subgroupOf (ctxO t tau x₁ x₂)).index = 2 := hrel
  by_cases hxR : x ∈ ctxR t tau x₁ x₂
  · exact Or.inl hxR
  · right
    have hx0 : (⟨x, hx⟩ : ↥(ctxO t tau x₁ x₂)) ∉
        (ctxR t tau x₁ x₂).subgroupOf (ctxO t tau x₁ x₂) := by
      intro h
      exact hxR (Subgroup.mem_subgroupOf.mp h)
    have ha0 : (⟨om, homO⟩ : ↥(ctxO t tau x₁ x₂)) ∉
        (ctxR t tau x₁ x₂).subgroupOf (ctxO t tau x₁ x₂) := by
      intro h
      exact homR (Subgroup.mem_subgroupOf.mp h)
    have hmul : (⟨om, homO⟩ : ↥(ctxO t tau x₁ x₂)) * (⟨x, hx⟩ : ↥(ctxO t tau x₁ x₂)) ∈
        (ctxR t tau x₁ x₂).subgroupOf (ctxO t tau x₁ x₂) := by
      rw [Subgroup.mul_mem_iff_of_index_two hH0]
      exact iff_of_false ha0 hx0
    have homxR : om * x ∈ ctxR t tau x₁ x₂ := by
      have h := hmul
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    exact ⟨om * x, homxR, by rw [← mul_assoc, hc.om_sq, one_mul]⟩

theorem c13K_invol_omR (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {r : G}
    (hr : r ∈ ctxR t tau x₁ x₂) (h2 : (om * r) ^ 2 = 1) :
    om * r ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G) := by
  obtain ⟨q, hq, hcases⟩ := c13K_mem_R_cases hc hr
  have homB : om ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have htauB : tau ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hqB : q ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({om, tau} : Set G) :=
    Subgroup.mem_sup_left hq
  rcases hcases with rfl | rfl | rfl | rfl
  · exact mul_mem homB hqB
  · exfalso
    obtain ⟨ht2, -, -, htau2, -, ht_tau, htau_om, -⟩ := c13K_rel hc
    have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hc.om_sq
    have homt : om * t * om = t * tau := by
      have h := hc.t_om
      rwa [hom_inv] at h
    have h_omt_sq : (om * t) ^ 2 = tau := by
      rw [pow_two]
      calc (om * t) * (om * t) = (om * t * om) * t := by group
        _ = (t * tau) * t := by rw [homt]
        _ = tau := by rw [ht_tau, mul_assoc, ← pow_two, ht2, mul_one]
    have hγM : om * t ∈ ctxM t tau x₁ x₂ :=
      mul_mem (c13K_mem_M hc).2.2.1 (c13K_mem_M hc).1
    exact (c13K_sq_ne_one_of_gamma hc hγM h_omt_sq hq)
      (by simpa only [mul_assoc] using h2)
  · rw [← mul_assoc]
    exact mul_mem (mul_mem homB htauB) hqB
  · exfalso
    obtain ⟨ht2, -, -, htau2, -, ht_tau, htau_om, -⟩ := c13K_rel hc
    have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hc.om_sq
    have homt : om * t * om = t * tau := by
      have h := hc.t_om
      rwa [hom_inv] at h
    have h_omt_sq : (om * t) ^ 2 = tau := by
      rw [pow_two]
      calc (om * t) * (om * t) = (om * t * om) * t := by group
        _ = (t * tau) * t := by rw [homt]
        _ = tau := by rw [ht_tau, mul_assoc, ← pow_two, ht2, mul_one]
    have hcomm : Commute (om * t) tau := by
      have h1 : Commute tau om := (commute_iff_eq tau om).mpr htau_om
      have h2 : Commute tau t := (commute_iff_eq tau t).mpr ht_tau.symm
      exact (h1.mul_right h2).symm
    have h_omttau_sq : (om * t * tau) ^ 2 = tau := by
      have h1 : om * t * tau = (om * t) * tau := by group
      rw [h1, hcomm.mul_pow 2, h_omt_sq, htau2, mul_one]
    have hγM : om * t * tau ∈ ctxM t tau x₁ x₂ :=
      mul_mem (mul_mem (c13K_mem_M hc).2.2.1 (c13K_mem_M hc).1) (c13K_mem_M hc).2.1
    exact (c13K_sq_ne_one_of_gamma hc hγM h_omttau_sq hq)
      (by simpa only [mul_assoc] using h2)

theorem c13K_tG_O (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g * t * g⁻¹ ∈ ctxO t tau x₁ x₂) : g * t * g⁻¹ ∈ ctxR t tau x₁ x₂ := by
  have hx2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [conj_pow, (c13K_rel hc).1, mul_one]
    exact mul_inv_cancel g
  rcases c13K_O_cases hc hg with hR | ⟨r, hr, hxr⟩
  · exact hR
  · exfalso
    have h2 : (om * r) ^ 2 = 1 := by rw [← hxr]; exact hx2
    exact hc.tG_Qom g (om * r) (c13K_invol_omR hc hr h2) hxr

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
