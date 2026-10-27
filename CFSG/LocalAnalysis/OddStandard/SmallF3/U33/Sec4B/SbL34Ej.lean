module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ej1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ej2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34 CFSG.OddStandard.SmallF3.HarrisU33.L34Z

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem fpf_core (ha : Ctx4A t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ ctxPL t tau x₁ x₂) (hc : rho * p * rho⁻¹ * p⁻¹ ∈ ctxO t tau x₁ x₂) :
    p ∈ ctxO t tau x₁ x₂ := by
  have hcQ := ha.toCtx4L.toCtx4Q
  have hs := isSylSL34_of_Ctx4L ha.toCtx4L
  have hc0M : rho * p * rho⁻¹ * p⁻¹ ∈ ctxM t tau x₁ x₂ := hcQ.O_le_M hc
  have hρM : rho ∈ ctxM t tau x₁ x₂ := hcQ.rho_mem_M
  have hρ1M : p * rho * p⁻¹ ∈ ctxM t tau x₁ x₂ := by
    have h : p * rho * p⁻¹ = (rho * p * rho⁻¹ * p⁻¹)⁻¹ * rho := by group
    rw [h]
    exact mul_mem (inv_mem hc0M) hρM
  have hρ1_3 : orderOf (p * rho * p⁻¹) = 3 := by
    have h : SemiconjBy p rho (p * rho * p⁻¹) := by
      show p * rho = (p * rho * p⁻¹) * p
      group
    rw [← SemiconjBy.orderOf_eq p h]
    exact hcQ.ord_rho
  obtain ⟨m, hmM, hmconj⟩ :=
    exists_conj_mem_zpowers (ctxM t tau x₁ x₂) ha.card_M hρ1M hρM hρ1_3 hcQ.ord_rho
  have hcL : m * p ∈ ctxLO t tau x₁ x₂ :=
    mul_mem (M_le_LO hcQ hs hmM) (Subgroup.mem_inf.mp hp).1
  have hcrho : (m * p) * rho * (m * p)⁻¹ ∈ zpowers rho := by
    have h : (m * p) * rho * (m * p)⁻¹ = m * (p * rho * p⁻¹) * m⁻¹ := by group
    rw [h]
    exact hmconj
  have hpM : p ∈ ctxM t tau x₁ x₂ := by
    have h : m⁻¹ * (m * p) ∈ ctxM t tau x₁ x₂ :=
      mul_mem (inv_mem hmM) (mem_M_of_conj_rho ha hcL hcrho)
    rwa [show m⁻¹ * (m * p) = p by group] at h
  rw [hcQ.O_eq_CV]
  exact Subgroup.mem_inf.mpr ⟨hpM, (Subgroup.mem_inf.mp hp).2⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
