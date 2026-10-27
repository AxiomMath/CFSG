module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15

theorem O89At.of_ctx2 (h : O89) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) : O89At G M := by
  intro H hH _
  obtain ⟨p, hp⟩ := ctx.p_mem
  exact h G ctx.standing ctx.uc M ctx.maxLocal ⟨p, hp, ctx.witness p hp⟩ ctx.strong H hH

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15