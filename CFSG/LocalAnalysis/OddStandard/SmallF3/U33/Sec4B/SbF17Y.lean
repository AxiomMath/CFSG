module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_Y_elem (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    exact IsZ4Z4E4.comm hc.q_iso ((mem_ctxYq_iff hc.q_iso a).mp a.2).1
      ((mem_ctxYq_iff hc.q_iso b).mp b.2).1
  · intro x hx
    exact ((mem_ctxYq_iff hc.q_iso x).mp hx).2

theorem l17_card_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card (ctxYq t tau x₁ x₂ rho) = 16 := by
  exact card_ctxYq hc.q_iso

theorem l17_Y_E16 (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    IsE16In 𝒮 (ctxYq t tau x₁ x₂ rho) := by
  exact ⟨(l17_le_sylow hc).2.1, l17_Y_elem hc.toCtx13, l17_card_Y hc.toCtx13⟩

theorem l17_Y_normal_sylow (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    NormalIn (ctxYq t tau x₁ x₂ rho) 𝒮 := by
  refine ⟨(l17_le_sylow hc).2.1, ?_⟩
  intro g hg k hk
  exact l17_K_normalizes_Y hc.toCtx13 g (hc.sylow.1 hg) k hk

theorem l17_tG_not_mem_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) (g : G) :
    g * t * g⁻¹ ∉ ctxYq t tau x₁ x₂ rho := by
  intro hmem
  exact (hc.tG_Qom g _ (Subgroup.mem_sup_left (ctxYq_le_ctxQ hmem))) rfl

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
