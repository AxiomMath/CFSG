module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18n
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbFit18

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l18_Xi_cap_cent_rho (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxXi, hxCent⟩ := Subgroup.mem_inf.mp hx
    have hxComm : x * rho = rho * x :=
      ((Subgroup.mem_centralizer_iff.mp hxCent) rho rfl).symm
    have hρ3 : rho ^ 3 = 1 := by
      rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
    have hQC : ctxQ t tau x₁ x₂ rho ≤ ctxCY t tau x₁ x₂ rho :=
      le_sup_left.trans (l18_QA_le_C hc.toCtx13)
    have hQn : ∀ c ∈ ctxCY t tau x₁ x₂ rho, ∀ q ∈ ctxQ t tau x₁ x₂ rho,
        c * q * c⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      intro c hcC q hq
      exact hc.normal_Q_K.2 c ((l18_C_normal hc.toCtx13).1 hcC) q hq
    have hρQ : ∀ q ∈ ctxQ t tau x₁ x₂ rho, rho * q * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
      intro q hq
      exact hc.normal_Q_K.2 rho (l17_mem_K hc.toCtx13).2.2.2.2 q hq
    have hρC : ∀ c ∈ ctxCY t tau x₁ x₂ rho, rho * c * rho⁻¹ ∈ ctxCY t tau x₁ x₂ rho := by
      intro c hcC
      exact (l18_C_normal hc.toCtx13).2 rho (l17_mem_K hc.toCtx13).2.2.2.2 c hcC
    have hab : ∀ c ∈ ctxCY t tau x₁ x₂ rho, ∀ c' ∈ ctxCY t tau x₁ x₂ rho,
        c * c' * c⁻¹ * c'⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      fun c h1 c' h2 => l18_comm_mem_Q hc.toCtx18 h1 h2
    have hxQ : x ∈ ctxQ t tau x₁ x₂ rho :=
      comm_zpowers_inf_cent_le (C := ctxCY t tau x₁ x₂ rho)
        (Q := ctxQ t tau x₁ x₂ rho) (ρ := rho) hρ3
        (l18_C_pgroup hc.toCtx13) hQC hQn hρQ hρC hab x
        (l18_Xi_le_comm_C hc hxXi) hxComm
    exact Subgroup.mem_bot.mpr
      (l17_CP_rho hc.toCtx13 x (l17_Q_le_P hc.toCtx13 hxQ) hxComm)
  · exact bot_le


end CFSG.OddStandard.SmallF3.HarrisU33.S4B
