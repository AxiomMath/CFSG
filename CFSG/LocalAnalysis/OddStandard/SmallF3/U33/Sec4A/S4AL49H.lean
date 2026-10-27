module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AProd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemXB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AA4

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma exists_mem_ctxM_conj_t_eq_tz (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) (h2 : 2 ∣ S.index)
    (hS1 : ∀ 𝒮 : Sylow 2 G, S < (𝒮 : Subgroup G) →
      ctxS1 S (𝒮 : Subgroup G) ≤ ctxM t tau x₁ x₂) :
    ∃ α ∈ ctxM t tau x₁ x₂, α * t * α⁻¹ = t * (x₁ * x₂) ^ 2 := by
  obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.toCtx0.isPGroup h2
  obtain ⟨hinv, _hidx, _hodd⟩ := sylow_facts_of_l42 h h2 𝒮 h𝒮
  obtain ⟨α, hαSyl, hαN, hα_notS⟩ :=
    exists_mem_normalizer_not_mem (show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup') h𝒮
  have hαS1 : α ∈ ctxS1 S (𝒮 : Subgroup G) := Subgroup.mem_inf.mpr ⟨hαN, hαSyl⟩
  refine ⟨α, hS1 𝒮 h𝒮 hαS1, ?_⟩
  have htZ : t ∈ S ⊓ centralizer (S : Set G) :=
    h.center_ge (Subgroup.subset_closure (by simp))
  have htS : t ∈ S := (Subgroup.mem_inf.mp htZ).1
  have htC : t ∈ centralizer (S : Set G) := (Subgroup.mem_inf.mp htZ).2
  have hmemS : α * t * α⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hαN t).mp htS
  have hmemC : α * t * α⁻¹ ∈ centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : α⁻¹ * s * α ∈ S := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hαN) s).mp hs
    have hcomm : (α⁻¹ * s * α) * t = t * (α⁻¹ * s * α) :=
      (Subgroup.mem_centralizer_iff.mp htC (α⁻¹ * s * α) hs')
    calc s * (α * t * α⁻¹) = α * (α⁻¹ * s * α) * t * α⁻¹ := by group
      _ = α * ((α⁻¹ * s * α) * t) * α⁻¹ := by group
      _ = α * (t * (α⁻¹ * s * α)) * α⁻¹ := by rw [hcomm]
      _ = (α * t * α⁻¹) * s := by group
  have hcenter : α * t * α⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} := by
    have hmem : α * t * α⁻¹ ∈ S ⊓ centralizer (S : Set G) := ⟨hmemS, hmemC⟩
    rwa [center_S_of h h43] at hmem
  rcases mem_closure_t_z h.toCtx0 hcenter with h1 | h1 | h1 | h1
  · exfalso
    have ht1 : t = 1 := by
      calc t = α⁻¹ * (α * t * α⁻¹) * α := by group
        _ = 1 := by rw [h1]; group
    exact t_ne_one h.hyp ht1
  · exfalso
    have hcomm : α * t = t * α := by
      calc α * t = (α * t * α⁻¹) * α := by group
        _ = t * α := by rw [h1]
    have hinvα : α ∈ invCent t := mem_invCent_iff.mpr hcomm
    exact hα_notS (hinv ▸ ⟨hinvα, hαSyl⟩)
  · exfalso
    exact not_conj_z_of_ctx h ⟨α, h1⟩
  · exact h1

theorem tF_subset_conjIn (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (h2 : 2 ∣ S.index)
    (hS1 : ∀ 𝒮 : Sylow 2 G, S < (𝒮 : Subgroup G) →
      ctxS1 S (𝒮 : Subgroup G) ≤ ctxM t tau x₁ x₂) :
    ∀ f ∈ fourGrp x₁ x₂, t * f ∈ conjIn (ctxM t tau x₁ x₂) t := by
  intro f hf
  have hM_eq : invCent t ⊓ ctxM t tau x₁ x₂ =
      ctxW t x₁ x₂ ⊔ closure {tau, rho, lam} := normalizer_X_of h h43 h44
  have hrho_in : rho ∈ invCent t ⊓ ctxM t tau x₁ x₂ := by
    rw [hM_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := (Subgroup.mem_inf.mp hrho_in).2
  have hrho_comm : rho * t = t * rho :=
    mem_invCent_iff.mp (Subgroup.mem_inf.mp hrho_in).1
  have hρt : rho * t * rho⁻¹ = t := by rw [hrho_comm]; group
  have hrhoinv_in : rho⁻¹ ∈ invCent t ⊓ ctxM t tau x₁ x₂ := by
    rw [hM_eq]
    exact Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  have hrhoinvM : rho⁻¹ ∈ ctxM t tau x₁ x₂ := (Subgroup.mem_inf.mp hrhoinv_in).2
  have hrhoinv_comm : rho⁻¹ * t = t * rho⁻¹ :=
    mem_invCent_iff.mp (Subgroup.mem_inf.mp hrhoinv_in).1
  have hρinvt : rho⁻¹ * t * rho = t := by rw [hrhoinv_comm]; group
  rcases mem_fourGrp_cases_rho h.toCtx0 hf with h1 | h1 | h1 | h1
  · subst h1
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  · subst h1
    obtain ⟨α, hαM, hαconj⟩ := exists_mem_ctxM_conj_t_eq_tz h h43 h44 h2 hS1
    exact ⟨α, hαM, hαconj⟩
  · subst h1
    obtain ⟨α, hαM, hαconj⟩ := exists_mem_ctxM_conj_t_eq_tz h h43 h44 h2 hS1
    refine ⟨rho * α, Subgroup.mul_mem _ hrhoM hαM, ?_⟩
    calc (rho * α) * t * (rho * α)⁻¹
        = rho * (α * t * α⁻¹) * rho⁻¹ := by group
      _ = rho * (t * (x₁ * x₂) ^ 2) * rho⁻¹ := by rw [hαconj]
      _ = (rho * t * rho⁻¹) * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) := by group
      _ = t * (rho * (x₁ * x₂) ^ 2 * rho⁻¹) := by rw [hρt]
  · subst h1
    obtain ⟨α, hαM, hαconj⟩ := exists_mem_ctxM_conj_t_eq_tz h h43 h44 h2 hS1
    refine ⟨rho⁻¹ * α, Subgroup.mul_mem _ hrhoinvM hαM, ?_⟩
    calc (rho⁻¹ * α) * t * (rho⁻¹ * α)⁻¹
        = rho⁻¹ * (α * t * α⁻¹) * rho := by group
      _ = rho⁻¹ * (t * (x₁ * x₂) ^ 2) * rho := by rw [hαconj]
      _ = (rho⁻¹ * t * rho) * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) := by group
      _ = t * (rho⁻¹ * (x₁ * x₂) ^ 2 * rho) := by rw [hρinvt]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
