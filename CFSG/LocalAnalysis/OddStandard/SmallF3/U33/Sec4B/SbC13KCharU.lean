module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KYc

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem c13K_charIn_Q_U (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    CharIn (ctxQ t tau x₁ x₂ rho) (ctxU t tau x₁ x₂ lam) ∧
      CharIn (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) (ctxU t tau x₁ x₂ lam) :=
  ⟨c13K_charIn_trans (c13K_lemma4_16 hc).2.1 (c13K_charIn_B_U hc),
    c13K_charIn_trans (c13K_lemma4_16 hc).2.2.1 (c13K_charIn_B_U hc)⟩

theorem c13K_charIn_V_U (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    CharIn (fourGrp x₁ x₂) (ctxU t tau x₁ x₂ lam) := by
  have hphi : (frattini ↥(ctxQ t tau x₁ x₂ rho)).map (ctxQ t tau x₁ x₂ rho).subtype =
      fourGrp x₁ x₂ := hc.phi_Q'
  have hVQ : fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho := by
    rw [← hphi]
    exact Subgroup.map_subtype_le _
  exact c13K_charIn_trans (charIn_of_map hVQ hphi inferInstance) (c13K_charIn_Q_U hc).1

theorem c13K_charIn_O_U (hc : Ctx13M t L S x₁ x₂ lam rho tau om) :
    CharIn (ctxO t tau x₁ x₂) (ctxU t tau x₁ x₂ lam) := by
  obtain ⟨hOU, hUM⟩ := c13K_O_le_U_le_M hc
  have heq : ctxU t tau x₁ x₂ lam ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      ctxO t tau x₁ x₂ := by
    apply le_antisymm
    · intro a ha
      have h : a ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
        ⟨hUM ha.1, ha.2⟩
      rwa [← hc.O_cent] at h
    · intro a ha
      have h : a ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
        rwa [← hc.O_cent]
      exact ⟨hOU ha, h.2⟩
  have h := L34Z.charIn_inf_centralizer (c13K_charIn_V_U hc)
  rwa [heq] at h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
