module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem ctx13_relations (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ^ 2 = 1 ∧ t ≠ 1 ∧ om ^ 2 = 1 ∧ tau ^ 2 = 1 ∧ tau ∉ zpowers t ∧ t * tau = tau * t ∧
      om * t * om⁻¹ = t * tau := by
  have ht2 : t ^ 2 = 1 := by
    rw [← hc.hyp.ord_t]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    have hord := hc.hyp.ord_t
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hτ2 : tau ^ 2 = 1 := hc.l44.1
  have hτH : tau ∈ invCent t := hc.le_invCent hc.tau_mem
  have htτ : t * tau = tau * t := (Subgroup.mem_centralizer_iff.mp hτH) t rfl
  have hτ : tau ∉ zpowers t := by
    intro hmem
    exact hc.tau_not_mem (by rw [hc.l43]; exact Subgroup.mem_sup_left hmem)
  exact ⟨ht2, ht1, hc.om_sq, hτ2, hτ, htτ, hc.t_om⟩

theorem ctx13_T_facts (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({t, om} : Set G) ≤ centralizer ({rho} : Set G) ∧
      IsPGroup 2 (closure ({t, om} : Set G)) ∧ Nat.card ↥(closure ({t, om} : Set G)) = 8 := by
  have hcard : Nat.card ↥(ctxCO t tau x₁ x₂ rho) = 8 := by
    obtain ⟨e⟩ := hc.CO_dihedral
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hO : IsPGroup 2 (ctxO t tau x₁ x₂) := isPGroup_pCoreOf (ctxM t tau x₁ x₂)
  have hCO : IsPGroup 2 (ctxCO t tau x₁ x₂ rho) := hO.to_le inf_le_left
  refine ⟨?_, ?_, ?_⟩
  · rw [← hc.CO_eq]
    exact inf_le_right
  · rw [← hc.CO_eq]
    exact hCO
  · rw [← hc.CO_eq]
    exact hcard

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
