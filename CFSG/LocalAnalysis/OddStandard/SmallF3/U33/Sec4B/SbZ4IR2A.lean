module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z

theorem z4i_lam_mem_NQ (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : lam ∈ ctxNQ t tau x₁ x₂ rho :=
  hz.z4i_M_le_NQ hz.lam_mem_M

theorem z4i_NQ_V (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {g a : G}
    (hg : g ∈ ctxNQ t tau x₁ x₂ rho) (ha : a ∈ fourGrp x₁ x₂) :
    g * a * g⁻¹ ∈ fourGrp x₁ x₂ := by
  obtain ⟨q, hq, rfl⟩ := (hz.V_eq_sq a).mp ha
  refine (hz.V_eq_sq _).mpr ⟨g * q * g⁻¹, (mem_set_normalizer_iff.mp hg q).mp hq, ?_⟩
  rw [conj_pow]

private def conjHom (g : G) : G →* G := (MulAut.conj g).toMonoidHom

private theorem conjHom_apply (g x : G) : conjHom g x = g * x * g⁻¹ := rfl

theorem z4i_NQ_norm_E (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {g e : G}
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

theorem z4i_norm_KI_of (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {g : G}
    (hg : g ∈ ctxNQ t tau x₁ x₂ rho) (hgt : g * t = t * g)
    (hgρ : g * rho * g⁻¹ ∈ zpowers rho) {k : G} (hk : k ∈ ctxKI t tau x₁ x₂ rho) :
    g * k * g⁻¹ ∈ ctxKI t tau x₁ x₂ rho := by
  have hk1 : k ∈ ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho := hk.1
  have hkNQ : k ∈ ctxNQ t tau x₁ x₂ rho := hk.2.1
  have hkc : k * t * k⁻¹ * t⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := hk.2.2
  rw [ctxKI, mem_inf]
  refine ⟨?_, ?_⟩
  · have hE : (ctxEcY t tau x₁ x₂ rho).map (conjHom g) ≤ ctxEcY t tau x₁ x₂ rho := by
      rintro y ⟨e, he, rfl⟩
      rw [conjHom_apply]
      exact hz.z4i_NQ_norm_E hg he
    have hC : (ctxCQ t tau x₁ x₂ rho).map (conjHom g) ≤ ctxCQ t tau x₁ x₂ rho := by
      rintro y ⟨c, hc, rfl⟩
      rw [conjHom_apply]
      exact conj_mem_ctxCQ hg hc
    have hZ : (zpowers rho).map (conjHom g) ≤ zpowers rho := by
      rintro y ⟨e, he, rfl⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
      rw [conjHom_apply, ← conj_zpow]
      exact zpow_mem hgρ n
    have hA : (⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆).map (conjHom g) ≤
        ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hE hZ
    have hsup : ((⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho)).map
        (conjHom g) ≤ ⁅ctxEcY t tau x₁ x₂ rho, zpowers rho⁆ ⊔ ctxCQ t tau x₁ x₂ rho := by
      rw [Subgroup.map_sup]
      exact sup_le (le_sup_of_le_left hA) (le_sup_of_le_right hC)
    exact hsup (Subgroup.mem_map_of_mem (conjHom g) hk1)
  · refine ⟨mul_mem (mul_mem hg hkNQ) (inv_mem hg), ?_⟩
    have hgt' : g * t * g⁻¹ = t := by rw [hgt]; group
    have hconj := conjugate_commutatorElement (g₁ := k) (g₂ := t) (g₃ := g)
    rw [hgt'] at hconj
    have hmem : g * ⁅k, t⁆ * g⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := conj_mem_ctxCQ hg hkc
    rw [hconj] at hmem
    simpa [commutatorElement_def] using hmem

theorem z4i_t_norm_KI (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ ctxKI t tau x₁ x₂ rho) : t * k * t⁻¹ ∈ ctxKI t tau x₁ x₂ rho :=
  hz.z4i_norm_KI_of hz.z4i_t_mem_NQ rfl
    (by rw [show t * rho * t⁻¹ = rho by rw [← hz.rho_comm_t]; group]; exact mem_zpowers rho) hk

theorem z4i_tau_norm_KI (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ ctxKI t tau x₁ x₂ rho) : tau * k * tau⁻¹ ∈ ctxKI t tau x₁ x₂ rho :=
  hz.z4i_norm_KI_of hz.z4i_tau_mem_NQ hz.t_comm_tau.symm
    (by rw [show tau * rho * tau⁻¹ = rho by rw [← hz.rho_comm_tau]; group]; exact mem_zpowers rho)
    hk

theorem z4i_lam_norm_KI (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ ctxKI t tau x₁ x₂ rho) : lam * k * lam⁻¹ ∈ ctxKI t tau x₁ x₂ rho :=
  hz.z4i_norm_KI_of hz.z4i_lam_mem_NQ hz.t_lam_comm.symm
    (by rw [hz.lam_rho]; exact inv_mem (mem_zpowers rho)) hk

theorem z4i_comm_t_KI (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ ctxKI t tau x₁ x₂ rho) : t * k * t⁻¹ * k⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := by
  have h : t * k * t⁻¹ * k⁻¹ = (k * t * k⁻¹ * t⁻¹)⁻¹ := by group
  rw [h]
  exact inv_mem hk.2.2

theorem z4i_rho_fpf_KC (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {k : G}
    (hk : k ∈ ctxKI t tau x₁ x₂ rho)
    (h : rho * k * rho⁻¹ * k⁻¹ ∈ ctxCQ t tau x₁ x₂ rho) : k ∈ ctxCQ t tau x₁ x₂ rho := by
  have hcomm : ∀ a b : ↥(ctxQ t tau x₁ x₂ rho), a * b = b * a :=
    fun a b => Subtype.ext (hz.Q_comm a.1 a.2 b.1 b.2)
  have h4 : ∀ q : ↥(ctxQ t tau x₁ x₂ rho), q ^ 4 = 1 := fun q =>
    Subtype.ext (by simpa using hz.Q_pow_four q.1 q.2)
  have hkNQ : k ∈ ctxNQ t tau x₁ x₂ rho := hk.2.1
  set κ : ↥(ctxKI t tau x₁ x₂ rho) := ⟨k, hk⟩ with hκ
  have hψ : z4iPsiK t tau x₁ x₂ rho κ ∈
      ⁅S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho), zpowers hz.z4iRhoBar⁆ := hz.z4iPsiK_mem_comm κ
  have hNQ : rho * k * rho⁻¹ * k⁻¹ ∈ ctxNQ t tau x₁ x₂ rho :=
    mul_mem (mul_mem (mul_mem hz.z4i_rho_mem_NQ hkNQ) (inv_mem hz.z4i_rho_mem_NQ))
      (inv_mem hkNQ)
  have h1 := (z4iPsi_eq_one_iff ⟨rho * k * rho⁻¹ * k⁻¹, hNQ⟩).mpr h
  have hfix : hz.z4iRhoBar * z4iPsiK t tau x₁ x₂ rho κ * hz.z4iRhoBar⁻¹ =
      z4iPsiK t tau x₁ x₂ rho κ := by
    have hsplit : (⟨rho * k * rho⁻¹ * k⁻¹, hNQ⟩ : ↥(ctxNQ t tau x₁ x₂ rho)) =
        ⟨rho, hz.z4i_rho_mem_NQ⟩ * ⟨k, hkNQ⟩ * ⟨rho, hz.z4i_rho_mem_NQ⟩⁻¹ * ⟨k, hkNQ⟩⁻¹ :=
      Subtype.ext rfl
    rw [hsplit, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hψ1 : z4iPsiK t tau x₁ x₂ rho κ = 1 :=
    S4B.z4i_fix_trivial (S4B.z4iFixY ↥(ctxQ t tau x₁ x₂ rho)) hz.z4iRhoBar
      hz.z4i_rhoBar_pow_three (fun e he => S4B.z4iFixY_conj_mem he _)
      (fun e he e' he' => S4B.z4iFixY_mul_comm hcomm h4 he he')
      (fun e he => S4B.z4iFixY_mul_self hcomm h4 he) hψ hfix
  exact (z4iPsi_eq_one_iff ⟨k, hkNQ⟩).mp hψ1

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
