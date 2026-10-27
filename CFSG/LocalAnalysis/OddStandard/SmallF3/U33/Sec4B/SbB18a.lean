module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_tau_om_mem_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxOK t tau x₁ x₂ rho ∧ tau ∈ ctxOK t tau x₁ x₂ rho ∧
      om ∈ ctxOK t tau x₁ x₂ rho := by
  have hR := l18_R_le_OK hc
  have hC := l18_C_le_OK hc
  have htR : t ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have htauR : tau ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have homC : om ∈ ctxCY t tau x₁ x₂ rho :=
    l18_QA_le_C hc (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  exact ⟨hR htR, hR htauR, hC homC⟩

theorem l18_O_le_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxO t tau x₁ x₂ ≤ ctxOK t tau x₁ x₂ rho := by
  rw [hc.toCtx11.O_eq, hc.CO_eq, l17_R_eq hc]
  refine sup_le (l18_R_le_OK hc) ?_
  rw [Subgroup.closure_le]
  rintro g (hg : g ∈ ({t, om} : Set G))
  rcases hg with rfl | rfl
  · exact (l18_tau_om_mem_OK hc).1
  · exact (l18_tau_om_mem_OK hc).2.2

theorem l18_Q_le_Xi (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ≤ ctxXi t tau x₁ x₂ rho := by
  rw [ctxQ, ctxXi]
  exact Subgroup.commutator_mono (l18_O_le_OK hc) le_rfl

theorem l18_Xi_le_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxXi t tau x₁ x₂ rho ≤ ctxOK t tau x₁ x₂ rho := by
  rw [ctxXi]
  refine Subgroup.commutator_le.mpr ?_
  intro x hx g hg
  have hgK : g ∈ ctxK t tau x₁ x₂ rho :=
    (Subgroup.zpowers_le.mpr (l17_mem_K hc).2.2.2.2) hg
  have hconj : g * x⁻¹ * g⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
    (l18_OK_normal).2 g hgK x⁻¹ (inv_mem hx)
  rw [commutatorElement_def]
  have h : x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
  rw [h]
  exact mul_mem hx hconj

theorem l18_Xi_pgroup (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    IsPGroup 2 (ctxXi t tau x₁ x₂ rho) :=
  (l18_OK_pgroup (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).to_le
    (l18_Xi_le_OK hc)

theorem l18_Xi_le_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ≤ 𝒮 :=
  (l18_Xi_le_OK hc.toCtx13).trans (l18_OK_le_sylow hc)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
