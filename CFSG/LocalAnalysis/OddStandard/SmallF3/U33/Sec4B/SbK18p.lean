module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18l
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18g

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem k18_t_conj_decomp (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {k : G}
    (hk : k ∈ ctxK t tau x₁ x₂ rho) :
    ∃ m ∈ ctxXi t tau x₁ x₂ rho,
      k * t * k⁻¹ = m * t * m⁻¹ ∨ k * t * k⁻¹ = m * (t * tau) * m⁻¹ := by
  have hK_eq : ctxK t tau x₁ x₂ rho =
      ctxOK t tau x₁ x₂ rho ⊔ closure ({rho, lam} : Set G) := hc.K_eq
  have hOKnorm : ∀ g ∈ closure ({rho, lam} : Set G), ∀ x ∈ ctxOK t tau x₁ x₂ rho,
      g * x * g⁻¹ ∈ ctxOK t tau x₁ x₂ rho := by
    intro g hg x hx
    have hgK : g ∈ ctxK t tau x₁ x₂ rho := by
      rw [hK_eq]
      exact Subgroup.mem_sup_right hg
    exact (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂)
      (rho := rho)).2 g hgK x hx
  have hk' : k ∈ ctxOK t tau x₁ x₂ rho ⊔ closure ({rho, lam} : Set G) := by
    rw [← hK_eq]
    exact hk
  obtain ⟨o, ho, h, hh, hk_eq⟩ := (mem_sup_iff_of_normalizes hOKnorm).mp hk'
  have ht_cent_rho : t ∈ centralizer ({rho} : Set G) := by
    have ht_inf : t ∈ ctxK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := by
      rw [hc.CK_rho]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    exact (Subgroup.mem_inf.mp ht_inf).2
  have hrho_comm : rho * t = t * rho := (Subgroup.mem_centralizer_iff.mp ht_cent_rho) rho rfl
  have hrho_cent : rho ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hrho_comm
  have hlam_cent : lam ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (l17_lam_comm hc).1
  have hcl_cent : closure ({rho, lam} : Set G) ≤ centralizer ({t} : Set G) :=
    (Subgroup.closure_le _).mpr (by
      intro g hg
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact hrho_cent
      · exact hlam_cent)
  have hh_comm : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.mp (hcl_cent hh)
  have hconj_h : h * t * h⁻¹ = t := by rw [hh_comm]; group
  have hXinorm : ∀ g ∈ closure ({t, om} : Set G), ∀ x ∈ ctxXi t tau x₁ x₂ rho,
      g * x * g⁻¹ ∈ ctxXi t tau x₁ x₂ rho := by
    intro g hg x hx
    have hgK : g ∈ ctxK t tau x₁ x₂ rho := by
      have hKmem := l17_mem_K hc
      have hle : closure ({t, om} : Set G) ≤ ctxK t tau x₁ x₂ rho :=
        (Subgroup.closure_le _).mpr (by
          intro y hy
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact hKmem.1
          · exact hKmem.2.2.1)
      exact hle hg
    exact (l18_Xi_normal hc).2 g hgK x hx
  have ho' : o ∈ ctxXi t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) := by
    rw [← k18_OK_eq_Xi_tom hc]
    exact ho
  obtain ⟨m, hm, h', hh', ho_eq⟩ := (mem_sup_iff_of_normalizes hXinorm).mp ho'
  refine ⟨m, hm, ?_⟩
  rw [hk_eq, ho_eq]
  have hLHS : ((m * h') * h) * t * ((m * h') * h)⁻¹ = m * (h' * t * h'⁻¹) * m⁻¹ := by
    calc ((m * h') * h) * t * ((m * h') * h)⁻¹
        = m * (h' * (h * t * h⁻¹) * h'⁻¹) * m⁻¹ := by group
      _ = m * (h' * t * h'⁻¹) * m⁻¹ := by rw [hconj_h]
  rw [hLHS]
  rcases l18_conj_t_D8 hc hh' with hc1 | hc2
  · exact Or.inl (by rw [hc1])
  · exact Or.inr (by rw [hc2])

private theorem k18_te_sq_om (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    (t * (q * om)) * (t * (q * om)) =
      ((t * q * t⁻¹) * (om * q⁻¹ * om⁻¹)) * tau := by
  obtain ⟨ht2pow, -, hom2pow, htau2pow, -, ht_tau, hom_t⟩ := ctx13_relations hc
  have ht2 : t * t = 1 := by rw [pow_two] at ht2pow; exact ht2pow
  have hom2 : om * om = 1 := by rw [pow_two] at hom2pow; exact hom2pow
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have homi : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2
  have hom_t' : t * om * t⁻¹ = om * tau := k18_t_om hc
  have homtau : om * tau = tau * om := by
    have homCO : om ∈ ctxCO t tau x₁ x₂ rho := by
      rw [hc.CO_eq]; exact Subgroup.subset_closure (by simp)
    have htau_cent_CO : tau ∈ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      have h : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
          centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
        rw [hc.CO_center]; exact Subgroup.mem_zpowers tau
      exact h.2
    exact Subgroup.mem_centralizer_iff.mp htau_cent_CO om homCO
  have htau_q : tau * q = q⁻¹ * tau := by
    calc tau * q = (tau * q * tau⁻¹) * tau := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = q⁻¹ * tau := by rw [hc.tau_inv_Q q hq]
  have hstep : t * q * om * t = (t * q * t⁻¹) * (om * tau) := by
    calc t * q * om * t = (t * q * t⁻¹) * (t * om * t⁻¹) * (t * t) := by group
      _ = (t * q * t⁻¹) * (om * tau) * 1 := by rw [hom_t', ht2]
      _ = (t * q * t⁻¹) * (om * tau) := by rw [mul_one]
  have hstep2 : (om * tau) * q * om = (om * q⁻¹ * om⁻¹) * tau := by
    calc (om * tau) * q * om = om * (tau * q) * om := by group
      _ = om * (q⁻¹ * tau) * om := by rw [htau_q]
      _ = om * q⁻¹ * (tau * om) := by group
      _ = om * q⁻¹ * (om * tau) := by rw [homtau]
      _ = (om * q⁻¹ * om) * tau := by group
      _ = (om * q⁻¹ * om⁻¹) * tau := by rw [homi]
  calc (t * (q * om)) * (t * (q * om))
      = (t * q * om * t) * q * om := by group
    _ = ((t * q * t⁻¹) * (om * tau)) * q * om := by rw [hstep]
    _ = (t * q * t⁻¹) * ((om * tau) * q * om) := by group
    _ = (t * q * t⁻¹) * ((om * q⁻¹ * om⁻¹) * tau) := by rw [hstep2]
    _ = ((t * q * t⁻¹) * (om * q⁻¹ * om⁻¹)) * tau := by group

private theorem k18_te_sq_tauom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {q : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) :
    (t * (q * (tau * om))) * (t * (q * (tau * om))) =
      ((t * q * t⁻¹) * (om * q * om⁻¹)) * tau := by
  obtain ⟨ht2pow, -, hom2pow, htau2pow, -, ht_tau, hom_t⟩ := ctx13_relations hc
  have ht2 : t * t = 1 := by rw [pow_two] at ht2pow; exact ht2pow
  have hom2 : om * om = 1 := by rw [pow_two] at hom2pow; exact hom2pow
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have homi : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2
  have htau2 : tau * tau = 1 := by rw [pow_two] at htau2pow; exact htau2pow
  have hom_t' : t * om * t⁻¹ = om * tau := k18_t_om hc
  have homtau : om * tau = tau * om := by
    have homCO : om ∈ ctxCO t tau x₁ x₂ rho := by
      rw [hc.CO_eq]; exact Subgroup.subset_closure (by simp)
    have htau_cent_CO : tau ∈ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      have h : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
          centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
        rw [hc.CO_center]; exact Subgroup.mem_zpowers tau
      exact h.2
    exact Subgroup.mem_centralizer_iff.mp htau_cent_CO om homCO
  have htau_conj : t * tau * t⁻¹ = tau := by rw [hti, ht_tau, mul_assoc, ht2, mul_one]
  have hstep : t * q * (tau * om) * t =
      (t * q * t⁻¹) * tau * (om * tau) := by
    calc t * q * (tau * om) * t
        = (t * q * t⁻¹) * (t * tau * t⁻¹) * (t * om * t⁻¹) * (t * t) := by group
      _ = (t * q * t⁻¹) * tau * (om * tau) * 1 := by rw [hom_t', htau_conj, ht2]
      _ = (t * q * t⁻¹) * tau * (om * tau) := by rw [mul_one]
  have hstep2 : tau * (om * tau) * q * tau * om = (om * q * om⁻¹) * tau := by
    calc tau * (om * tau) * q * tau * om = tau * (tau * om) * q * tau * om := by rw [homtau]
      _ = om * q * tau * om := by rw [← mul_assoc, ← pow_two, htau2pow, one_mul]
      _ = om * q * (tau * om) := by group
      _ = om * q * (om * tau) := by rw [homtau]
      _ = (om * q * om) * tau := by group
      _ = (om * q * om⁻¹) * tau := by rw [homi]
  calc (t * (q * (tau * om))) * (t * (q * (tau * om)))
      = (t * q * (tau * om) * t) * q * (tau * om) := by group
    _ = ((t * q * t⁻¹) * tau * (om * tau)) * q * (tau * om) := by rw [hstep]
    _ = (t * q * t⁻¹) * (tau * (om * tau) * q * tau * om) := by group
    _ = (t * q * t⁻¹) * ((om * q * om⁻¹) * tau) := by rw [hstep2]
    _ = ((t * q * t⁻¹) * (om * q * om⁻¹)) * tau := by group

theorem k18_te_sq_ne (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {q a : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) (ha : a = om ∨ a = tau * om) :
    (t * (q * a)) * (t * (q * a)) ≠ 1 := by
  have htK : t ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).1
  have homK : om ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.1
  intro hX
  rcases ha with ha | ha
  · rw [ha] at hX
    rw [k18_te_sq_om hc hq] at hX
    have hq₁ : t * q * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hc.normal_Q_K.2 t htK q hq
    have hq₃ : om * q⁻¹ * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.normal_Q_K.2 om homK q⁻¹ (inv_mem hq)
    have hA : ((t * q * t⁻¹) * (om * q⁻¹ * om⁻¹)) ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hq₁ hq₃
    have htau_inv : tau⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      rw [← eq_inv_of_mul_eq_one_left hX]
      exact hA
    have htau_mem : tau ∈ ctxQ t tau x₁ x₂ rho := by
      have := inv_mem htau_inv
      simpa only [inv_inv] using this
    exact Ctx13.tau_not_mem_Q hc htau_mem
  · rw [ha] at hX
    rw [k18_te_sq_tauom hc hq] at hX
    have hq₁ : t * q * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hc.normal_Q_K.2 t htK q hq
    have hq₃ : om * q * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hc.normal_Q_K.2 om homK q hq
    have hA : ((t * q * t⁻¹) * (om * q * om⁻¹)) ∈ ctxQ t tau x₁ x₂ rho :=
      mul_mem hq₁ hq₃
    have htau_inv : tau⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      rw [← eq_inv_of_mul_eq_one_left hX]
      exact hA
    have htau_mem : tau ∈ ctxQ t tau x₁ x₂ rho := by
      have := inv_mem htau_inv
      simpa only [inv_inv] using this
    exact Ctx13.tau_not_mem_Q hc htau_mem


end CFSG.OddStandard.SmallF3.HarrisU33.S4B
