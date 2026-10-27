module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCStepsDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41FusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4F

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

theorem fzc_steps
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) : FzCSteps t L S x₁ x₂ lam rho := by
  have p0 : L41GCtx t L S x₁ x₂ lam rho := ⟨h.ctx, h.eq_PL⟩
  have p1 : L41GPh1 t L S x₁ x₂ lam rho := ⟨p0, S4A.l41_basic_of p0⟩
  have p2 : L41GPh2 t L S x₁ x₂ lam rho := ⟨p1, S4A.l41_sylow_of p1 h.ass⟩
  have p3 : L41GPh3 t L S x₁ x₂ lam rho := ⟨p2, S4A.l41_fusion_of p2⟩
  have n0 := S4A.l41_normalizer0_of p3
  exact ⟨h.ctx, p3.basic, p3.fusion, n0.orbit_t, n0.O2_eq, n0.card_O2, n0.N_eq, n0.V_le,
    n0.V_pGroup, n0.V_sylow, n0.card_V⟩

end CFSG.OddStandard.SmallF3.FritzII
