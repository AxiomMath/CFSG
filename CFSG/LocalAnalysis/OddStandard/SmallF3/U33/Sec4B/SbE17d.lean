module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbE17c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_F3_om (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {p : G}
    (hp : p ∈ ctxP t tau x₁ x₂ rho) {a : G} (ha : a = om ∨ a = om * tau) :
    (t * (p * a)) * (t * (p * a)) ≠ 1 := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc
  obtain ⟨htK, htauK, homK, -, -⟩ := l17_mem_K hc
  have ht2' : t * t = 1 := by rwa [pow_two] at ht2
  have hom2' : om * om = 1 := by rwa [pow_two] at hom2
  have htau2' : tau * tau = 1 := by rwa [pow_two] at htau2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2'
  have htau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau2'
  have hcomm : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  have hτtτ : tau * t * tau = t := by
    rw [ht_tau.symm, mul_assoc, htau2', mul_one]
  have haK : a ∈ ctxK t tau x₁ x₂ rho := by
    rcases ha with rfl | rfl
    · exact homK
    · exact (ctxK t tau x₁ x₂ rho).mul_mem homK htauK
  have ha2 : a * a = 1 := by
    rcases ha with rfl | rfl
    · exact hom2'
    · calc (om * tau) * (om * tau) = om * (tau * om) * tau := by group
        _ = om * (om * tau) * tau := by rw [← hcomm]
        _ = (om * om) * (tau * tau) := by group
        _ = 1 := by rw [hom2', htau2', mul_one]
  have hconj : a * t * a⁻¹ = t * tau := by
    rcases ha with rfl | rfl
    · simpa [hom_inv] using hom_t
    · calc (om * tau) * t * (om * tau)⁻¹
          = om * (tau * t * tau⁻¹) * om⁻¹ := by group
        _ = om * t * om⁻¹ := by rw [htau_inv, hτtτ]
        _ = t * tau := hom_t
  refine fun hzero => ?_
  have hp1 : t * p * t⁻¹ ∈ ctxP t tau x₁ x₂ rho := (l17_P_normal hc).2 t htK p hp
  have hp2 : a * p * a⁻¹ ∈ ctxP t tau x₁ x₂ rho := (l17_P_normal hc).2 a haK p hp
  have h1 : a * t = (t * tau) * a := by
    have h := congrArg (fun z => z * a) hconj
    simpa [mul_assoc] using h
  have hsq : (t * (p * a)) * (t * (p * a)) =
      (t * p * t⁻¹) * tau * (a * p * a⁻¹) := by
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    calc (t * (p * a)) * (t * (p * a)) = (t * p) * (a * t) * (p * a) := by group
      _ = (t * p) * ((t * tau) * a) * (p * a) := by rw [h1]
      _ = (t * p * t⁻¹) * tau * (a * p * a⁻¹) := by
            rw [ht_inv, ha_inv]; group
  rw [hsq] at hzero
  have hprod : (t * p * t⁻¹)⁻¹ * (a * p * a⁻¹)⁻¹ = tau := by
    have h1' : tau = (t * p * t⁻¹)⁻¹ *
        ((t * p * t⁻¹) * tau * (a * p * a⁻¹)) * (a * p * a⁻¹)⁻¹ := by group
    rw [hzero, mul_one] at h1'
    exact h1'.symm
  have hm : (t * p * t⁻¹)⁻¹ * (a * p * a⁻¹)⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
    (ctxP t tau x₁ x₂ rho).mul_mem
      ((ctxP t tau x₁ x₂ rho).inv_mem hp1) ((ctxP t tau x₁ x₂ rho).inv_mem hp2)
  exact l17_tau_not_mem_P hc (hprod ▸ hm)

theorem l17_F3 (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) {e : G}
    (he : e ∈ ctxE0 t tau x₁ x₂ rho om) (h2 : (t * e) * (t * e) = 1) :
    ∃ x ∈ ctxE0 t tau x₁ x₂ rho om, t * e = x * t * x⁻¹ := by
  obtain ⟨p, hp, a, ha, rfl⟩ := (l17_mem_E0 hc.toCtx13).mp he
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc.toCtx13
  obtain ⟨htK, htauK, homK, -, -⟩ := l17_mem_K hc.toCtx13
  have ht2' : t * t = 1 := by rwa [pow_two] at ht2
  have hτ2' : tau * tau = 1 := by rwa [pow_two] at htau2
  have hom2' : om * om = 1 := by rwa [pow_two] at hom2
  have hτ_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hτ2'
  have hcomm : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  have hlist := (mem_closure_pair_of_invol (a := tau) (b := om) hτ2' hom2' hcomm.symm).mp ha
  rcases hlist with h | h | h | h
  ·
    subst a
    have hp2 : (t * p) * (t * p) = 1 := by simpa using h2
    obtain ⟨q, hq, hqe⟩ :=
      l17_fl_ctx (g := t) hc ht2' htK (l17_card_CY_t hc.toCtx13) p hp hp2
    exact ⟨q, Subgroup.mem_sup_left hq, by simpa using hqe⟩
  ·
    subst a
    have hgK : t * tau ∈ ctxK t tau x₁ x₂ rho :=
      (ctxK t tau x₁ x₂ rho).mul_mem htK htauK
    have hg2 : (t * tau) * (t * tau) = 1 := by
      calc (t * tau) * (t * tau) = t * (tau * t) * tau := by group
        _ = t * (t * tau) * tau := by rw [ht_tau.symm]
        _ = (t * t) * (tau * tau) := by group
        _ = 1 := by rw [ht2', hτ2', mul_one]
    have hxP : tau * p * tau⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
      (l17_P_normal hc.toCtx13).2 tau htauK p hp
    have hgx : (t * tau) * (tau * p * tau⁻¹) = t * (p * tau) := by
      calc (t * tau) * (tau * p * tau⁻¹) = t * (tau * tau) * p * tau⁻¹ := by group
        _ = t * p * tau⁻¹ := by rw [hτ2', mul_one]
        _ = t * (p * tau) := by rw [hτ_inv]; group
    have hgx2 : ((t * tau) * (tau * p * tau⁻¹)) *
        ((t * tau) * (tau * p * tau⁻¹)) = 1 := by
      rw [hgx]; exact h2
    obtain ⟨q, hq, hqe⟩ :=
      l17_fl_ctx (g := t * tau) hc hg2 hgK (l17_card_CY_ttau hc.toCtx13)
        (tau * p * tau⁻¹) hxP hgx2
    have hconj : q * (t * tau) * q⁻¹ = (q * om) * t * (q * om)⁻¹ := by
      rw [hom_t.symm]; group
    refine ⟨q * om, ?_, ?_⟩
    · have homE : om ∈ ctxE0 t tau x₁ x₂ rho om :=
        Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      exact (ctxE0 t tau x₁ x₂ rho om).mul_mem (Subgroup.mem_sup_left hq) homE
    · calc t * (p * tau) = (t * tau) * (tau * p * tau⁻¹) := hgx.symm
        _ = q * (t * tau) * q⁻¹ := hqe
        _ = (q * om) * t * (q * om)⁻¹ := hconj
  ·
    subst a
    exact absurd h2 (l17_F3_om hc.toCtx13 hp (Or.inl rfl))
  ·
    subst a
    exact absurd h2 (l17_F3_om hc.toCtx13 hp (Or.inr hcomm.symm))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
