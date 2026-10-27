module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IStmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4FA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

private def conjHom (g : G) : G →* G := (MulAut.conj g).toMonoidHom

private theorem conjHom_apply (g x : G) : conjHom g x = g * x * g⁻¹ := rfl

theorem z4i_M_le_NQ (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ ≤ ctxNQ t tau x₁ x₂ rho := by
  intro g hg
  rw [ctxNQ, mem_set_normalizer_iff]
  intro h
  constructor
  · exact hz.normal_Q.2 g hg h
  · intro hh
    have h1 := hz.normal_Q.2 g⁻¹ (inv_mem hg) (g * h * g⁻¹) hh
    have h2 : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
    rwa [h2] at h1

theorem z4i_t_mem_NQ (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : t ∈ ctxNQ t tau x₁ x₂ rho :=
  hz.z4i_M_le_NQ hz.t_mem_M

theorem z4i_tau_mem_NQ (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : tau ∈ ctxNQ t tau x₁ x₂ rho :=
  hz.z4i_M_le_NQ hz.tau_mem_M

theorem z4i_rho_mem_NQ (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : rho ∈ ctxNQ t tau x₁ x₂ rho :=
  hz.z4i_M_le_NQ hz.rho_mem_M

theorem z4i_NQ_Y (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {g a : G}
    (hg : g ∈ ctxNQ t tau x₁ x₂ rho) (ha : a ∈ ctxYq t tau x₁ x₂ rho) :
    g * a * g⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
  rw [hz.mem_Y_iff]
  have haY := (hz.mem_Y_iff a).mp ha
  refine ⟨?_, ?_⟩
  · exact (mem_set_normalizer_iff.mp hg a).mp (hz.Y_le_Q ha)
  · rw [conj_pow, haY.2]
    group

private theorem NQ_norm_E (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {g e : G}
    (hg : g ∈ ctxNQ t tau x₁ x₂ rho) (he : e ∈ ctxEcY t tau x₁ x₂ rho) :
    g * e * g⁻¹ ∈ ctxEcY t tau x₁ x₂ rho := by
  rw [ctxEcY, mem_inf]
  refine ⟨mul_mem (mul_mem hg he.1) (inv_mem hg), ?_⟩
  rw [mem_centralizer_iff]
  intro a ha
  have ha' : g⁻¹ * a * g ∈ ctxYq t tau x₁ x₂ rho := by
    simpa using hz.z4i_NQ_Y (inv_mem hg) ha
  have h1 : (g⁻¹ * a * g) * e = e * (g⁻¹ * a * g) :=
    (mem_centralizer_iff.mp he.2) _ ha'
  calc a * (g * e * g⁻¹) = g * ((g⁻¹ * a * g) * e) * g⁻¹ := by group
    _ = g * (e * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = (g * e * g⁻¹) * a := by group

theorem z4i_C_le_E (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxCQ t tau x₁ x₂ rho ≤ ctxEcY t tau x₁ x₂ rho := by
  intro c hc
  rw [ctxEcY, mem_inf]
  exact ⟨ctxCQ_le_ctxNQ t tau x₁ x₂ rho hc, centralizer_le hz.Y_le_Q hc⟩

theorem z4i_C_le_CtI (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxCQ t tau x₁ x₂ rho ≤ ctxCtI t tau x₁ x₂ rho := by
  intro c hc
  refine ⟨ctxCQ_le_ctxNQ t tau x₁ x₂ rho hc, ?_⟩
  have h1 : c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) := by group
  rw [h1]
  exact mul_mem hc (conj_mem_ctxCQ hz.z4i_t_mem_NQ (inv_mem hc))

theorem z4i_C_le_KI (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxCQ t tau x₁ x₂ rho ≤ ctxKI t tau x₁ x₂ rho := by
  intro c hc
  rw [ctxKI, mem_inf]
  exact ⟨(le_sup_right : ctxCQ t tau x₁ x₂ rho ≤
    ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho) hc, z4i_C_le_CtI hz hc⟩

theorem z4i_rho_norm_E (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {e : G}
    (he : e ∈ ctxEcY t tau x₁ x₂ rho) : rho * e * rho⁻¹ ∈ ctxEcY t tau x₁ x₂ rho :=
  NQ_norm_E hz hz.z4i_rho_mem_NQ he

theorem z4i_comm_E_le_E (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ≤ ctxEcY t tau x₁ x₂ rho := by
  rw [Subgroup.commutator_le]
  intro e he g hg
  have hgNQ : g ∈ ctxNQ t tau x₁ x₂ rho := Subgroup.zpowers_le.mpr hz.z4i_rho_mem_NQ hg
  have hconj : g * e⁻¹ * g⁻¹ ∈ ctxEcY t tau x₁ x₂ rho := NQ_norm_E hz hgNQ (inv_mem he)
  have hcomm : ⁅e, g⁆ = e * (g * e⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
  rw [hcomm]
  exact mul_mem he hconj

theorem z4i_KI_le_E (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    ctxKI t tau x₁ x₂ rho ≤ ctxEcY t tau x₁ x₂ rho := by
  intro k hk
  exact sup_le (z4i_comm_E_le_E hz) (z4i_C_le_E hz) hk.1

theorem z4i_rho_norm_KI (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ ctxKI t tau x₁ x₂ rho) : rho * k * rho⁻¹ ∈ ctxKI t tau x₁ x₂ rho := by
  have hk1 : k ∈ ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho := hk.1
  have hkNQ : k ∈ ctxNQ t tau x₁ x₂ rho := hk.2.1
  have hkc : k * t * k⁻¹ * t⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := hk.2.2
  rw [ctxKI, mem_inf]
  refine ⟨?_, ?_⟩
  · have hE : (ctxEcY t tau x₁ x₂ rho).map (conjHom rho) ≤ ctxEcY t tau x₁ x₂ rho := by
      rintro y ⟨e, he, rfl⟩
      rw [conjHom_apply]
      exact z4i_rho_norm_E hz he
    have hC : (ctxCQ t tau x₁ x₂ rho).map (conjHom rho) ≤ ctxCQ t tau x₁ x₂ rho := by
      rintro y ⟨c, hc, rfl⟩
      rw [conjHom_apply]
      exact conj_mem_ctxCQ hz.z4i_rho_mem_NQ hc
    have hρ : conjHom rho rho = rho := by rw [conjHom_apply]; group
    have hA : (⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆).map (conjHom rho) ≤
        ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ := by
      rw [Subgroup.map_commutator]
      rw [MonoidHom.map_zpowers (conjHom rho) rho, hρ]
      exact Subgroup.commutator_mono hE le_rfl
    have hsup : ((⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho)).map
        (conjHom rho) ≤
        ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho := by
      rw [Subgroup.map_sup]
      exact sup_le (le_sup_of_le_left hA) (le_sup_of_le_right hC)
    exact hsup (Subgroup.mem_map_of_mem (conjHom rho) hk1)
  · refine ⟨mul_mem (mul_mem hz.z4i_rho_mem_NQ hkNQ) (inv_mem hz.z4i_rho_mem_NQ), ?_⟩
    have hρt : rho * t * rho⁻¹ = t := by rw [hz.rho_comm_t]; group
    have hconj := conjugate_commutatorElement (g₁ := k) (g₂ := t) (g₃ := rho)
    rw [hρt] at hconj
    have hmem : rho * ⁅k, t⁆ * rho⁻¹ ∈ ctxCQ t tau x₁ x₂ rho :=
      conj_mem_ctxCQ hz.z4i_rho_mem_NQ hkc
    rw [hconj] at hmem
    simpa [commutatorElement_def] using hmem

theorem z4i_tau_not_mem_C (hz : Ctx4Z t L S x₁ x₂ lam rho tau) :
    tau ∉ ctxCQ t tau x₁ x₂ rho := by
  intro htau
  have hcomm : x₁ * tau = tau * x₁ := (mem_centralizer_iff.mp htau) x₁ hz.x₁_mem_Q
  have h1 : tau * x₁ * tau⁻¹ = x₁ := by rw [← hcomm]; group
  have h2 : tau * x₁ * tau⁻¹ = x₁⁻¹ := hz.tau_inv_Q x₁ hz.x₁_mem_Q
  have h3 : x₁ = x₁⁻¹ := h1.symm.trans h2
  exact hz.y_ne_one (by rw [pow_two]; exact inv_eq_iff_mul_eq_one.mp h3.symm)

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
