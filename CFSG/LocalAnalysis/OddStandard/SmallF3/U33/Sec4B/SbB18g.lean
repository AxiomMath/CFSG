module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem l18_conj_t_closure_aux (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ h ∈ closure ({t, om} : Set G),
      (h * t * h⁻¹ = t ∨ h * t * h⁻¹ = t * tau) ∧ h * tau = tau * h := by
  obtain ⟨ht2, _ht1, hom2, htau2, _htau_not, httau, hom_t⟩ := ctx13_relations hc
  have hcomm_tau : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 httau hom_t
  intro h hh
  refine Subgroup.closure_induction (p := fun h _ =>
      (h * t * h⁻¹ = t ∨ h * t * h⁻¹ = t * tau) ∧ h * tau = tau * h) ?_ ?_ ?_ ?_ hh
  · intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨Or.inl (by group), httau⟩
    · exact ⟨Or.inr hom_t, hcomm_tau⟩
  · exact ⟨Or.inl (by group), by group⟩
  · intro x y _hx _hy ihx ihy
    obtain ⟨ihx1, ihx2⟩ := ihx
    obtain ⟨ihy1, ihy2⟩ := ihy
    refine ⟨?_, ?_⟩
    · have hmul : (x * y) * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
      rw [hmul]
      rcases ihy1 with hy1 | hy2
      · rw [hy1]; exact ihx1
      · rw [hy2]
        have hconj : x * (t * tau) * x⁻¹ = (x * t * x⁻¹) * tau := by
          calc x * (t * tau) * x⁻¹ = (x * t * x⁻¹) * (x * tau * x⁻¹) := by group
            _ = (x * t * x⁻¹) * tau := by rw [ihx2]; group
        rw [hconj]
        rcases ihx1 with hx1 | hx2
        · exact Or.inr (by rw [hx1])
        · exact Or.inl (by rw [hx2, mul_assoc, ← pow_two, htau2, mul_one])
    · calc (x * y) * tau = x * (y * tau) := by group
        _ = x * (tau * y) := by rw [ihy2]
        _ = (x * tau) * y := by group
        _ = (tau * x) * y := by rw [ihx2]
        _ = tau * (x * y) := by group
  · intro x _hx ih
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · rcases ih1 with hx1 | hx2
      · left
        calc x⁻¹ * t * x⁻¹⁻¹ = x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ := by rw [hx1]
          _ = t := by group
      · right
        have h2 : (x⁻¹ * t * x⁻¹⁻¹) * tau = t := by
          calc (x⁻¹ * t * x⁻¹⁻¹) * tau = x⁻¹ * t * (x⁻¹⁻¹ * tau) := by group
            _ = x⁻¹ * t * (x * tau) := by rw [inv_inv]
            _ = x⁻¹ * t * (tau * x) := by rw [ih2]
            _ = x⁻¹ * (t * tau) * x := by group
            _ = x⁻¹ * (x * t * x⁻¹) * x := by rw [← hx2]
            _ = t := by group
        calc x⁻¹ * t * x⁻¹⁻¹ = (x⁻¹ * t * x⁻¹⁻¹) * (tau * tau) := by
              rw [← pow_two, htau2, mul_one]
          _ = ((x⁻¹ * t * x⁻¹⁻¹) * tau) * tau := by group
          _ = t * tau := by rw [h2]
    · calc x⁻¹ * tau = x⁻¹ * tau * x * x⁻¹ := by group
        _ = x⁻¹ * (tau * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * tau) * x⁻¹ := by rw [← ih2]
        _ = tau * x⁻¹ := by group

theorem l18_conj_t_D8 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {h : G}
    (hh : h ∈ closure ({t, om} : Set G)) : h * t * h⁻¹ = t ∨ h * t * h⁻¹ = t * tau :=
  (l18_conj_t_closure_aux hc h hh).1

theorem l18_t_conj_decomp (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {k : G}
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
    Subgroup.mem_centralizer_singleton_iff.mpr (l17_lam_comm hc.toCtx13).1
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
      have hKmem := l17_mem_K hc.toCtx13
      have hle : closure ({t, om} : Set G) ≤ ctxK t tau x₁ x₂ rho :=
        (Subgroup.closure_le _).mpr (by
          intro y hy
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact hKmem.1
          · exact hKmem.2.2.1)
      exact hle hg
    exact (l18_Xi_normal hc.toCtx13).2 g hgK x hx
  have ho' : o ∈ ctxXi t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) := by
    rw [← l18_OK_eq_Xi_sup hc]
    exact ho
  obtain ⟨m, hm, h', hh', ho_eq⟩ := (mem_sup_iff_of_normalizes hXinorm).mp ho'
  refine ⟨m, hm, ?_⟩
  rw [hk_eq, ho_eq]
  have hLHS : ((m * h') * h) * t * ((m * h') * h)⁻¹ = m * (h' * t * h'⁻¹) * m⁻¹ := by
    calc ((m * h') * h) * t * ((m * h') * h)⁻¹
        = m * (h' * (h * t * h⁻¹) * h'⁻¹) * m⁻¹ := by group
      _ = m * (h' * t * h'⁻¹) * m⁻¹ := by rw [hconj_h]
  rw [hLHS]
  rcases l18_conj_t_D8 hc.toCtx13 hh' with hc1 | hc2
  · exact Or.inl (by rw [hc1])
  · exact Or.inr (by rw [hc2])

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
