module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Y

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

open KFactsPair in
theorem row1511'_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hK518 : K518) (hK517 : K517_6) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hK89 : K89Sp)
    (hK3 : K3DvdL3)
    (hLift : ∀ Ls, GNYComponent (T.subgroupOf M) T₁ T₂ Ls → ∃ L, LiftOf (T.subgroupOf M) L Ls)
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂) :
    Row1511 G M T T₁ T₂ := by
  show 3 ∉ sigmaM G M
  intro h3
  obtain ⟨Ls₀, hLs₀, -⟩ := exists_yComponent_dvd_ctx_gen kWiel_holds kHupAt_three ctx h3
  obtain ⟨L₀, hL₀⟩ := hLift Ls₀ hLs₀
  obtain ⟨Ls, hLs, hnorm, hC, hle, hy, -, hcase⟩ :=
    xlevel_three_branch_gen hK518 hK517 ctx.gn
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.good ctx) (ctx.rank_N₁ 3 h3)
      (ctx.rank_N₂ 3 h3) (ctx.three_le 3 h3) hLs₀ hL₀
  obtain ⟨L, hL⟩ := hLift Ls hLs
  rcases hcase with hU | ⟨-, hL3⟩
  · exact ctx.noU4 3 h3 (u4Shape_of_u4Data M
      (u4Data_of_lift hKSMU4 ctx.gn hLs.1 hnorm hL hC hle hy hU))
  · have key : ∀ Ti : Subgroup ↥M, Ti ≠ ⊥ → Ti ≤ T.subgroupOf M →
        (Ti.subgroupOf (T.subgroupOf M)).Characteristic →
        CFSG.Open.pRank 3 (normalizer (Ti : Set ↥M)) ≤ 1 →
        HasLThreeCore (gnA (T.subgroupOf M) Ti Ls) → False := by
      intro Ti hne hle' hchar hrk hL3'
      obtain ⟨Y, hYle, hYq⟩ := exists_Y_O2form hKSML3 ctx.gn hLs.1 hL hC hL3'
      exact false_of_Y_O2form_gen hK89 hK3 ctx.cstar.toStandingGen ctx.sylow ctx.notLe
        (ctx.strong 3 h3) hne hle' hchar hrk hYle hYq
    rcases hL3 with h | h
    · exact key T₁ ctx.pair.ne_bot₁ (ctx.pair.le_center.trans (omegaOneCenterOf_le_subgroup _))
        ctx.pair.char₁ (ctx.rank_N₁ 3 h3) h
    · exact key T₂ ctx.pair.ne_bot₂ ctx.pair.le₂ ctx.pair.char₂ (ctx.rank_N₂ 3 h3) h

open KFactsPair in
theorem row1511' {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hK518 : K518) (hK517 : K517_6) (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hK89 : K89Sp)
    (hK3 : K3DvdL3)
    (hLift : ∀ Ls, GNYComponent (T.subgroupOf M) T₁ T₂ Ls → ∃ L, LiftOf (T.subgroupOf M) L Ls)
    (ctx : S15Ctx2 G M T T₁ T₂) : Row1511 G M T T₁ T₂ :=
  row1511'_gen hK518 hK517 hKSMU4 hKSML3 hK89 hK3 hLift
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx)

end CFSG.LocalAnalysis.RankThreeUC.S15
