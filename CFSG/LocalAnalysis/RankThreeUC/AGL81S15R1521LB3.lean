module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PG
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PH
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KHupGeFive

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section Row1524Ctx

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

theorem row1524_gen (k534 : K534) (kA6Z3 : KA6Z3) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (h22 : Row1522 G M T T₁ T₂) : Row1524 G M T T₁ T₂ := by
  intro Ls L hLs hL h3
  have hle : Ls ≤ gnImg (T.subgroupOf M) (Subgroup.normalClosure (L : Set ↥M)) := by
    rw [← hL.2]
    exact Subgroup.map_mono Subgroup.le_normalClosure
  rcases h22 Ls L hLs hL _ rfl _ rfl with h1 | ⟨h2, -⟩ | h3' | ⟨hcp, -⟩
  · exact false_of_isAltSixCoverThree_le hLs.1 hle h3 (Or.inl (Or.inl h1))
  · exact false_of_isAltSixCoverThree_le hLs.1 hle h3 (Or.inr h2)
  · rcases h3' with h6 | h8 | h5 | hU
    · exact false_of_isAltSixCoverThree_le hLs.1 hle h3 (Or.inl (Or.inr (Or.inl h6)))
    · exact false_of_isAltSixCoverThree_le hLs.1 hle h3 (Or.inl (Or.inr (Or.inr (Or.inl h8))))
    · exact false_of_isAltSixCoverThree_le hLs.1 hle h3
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
    · exact false_of_isAltSixCoverThree_le hLs.1 hle h3
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hU)))))
  · exact false_of_centralProd_gn k534 kA6Z3 ctx.gn hLs.1 (ctx.good.shape Ls hLs).1 h3 hle hcp

theorem row1524 (k534 : K534) (kA6Z3 : KA6Z3) {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) (h22 : Row1522 G M T T₁ T₂) :
    Row1524 G M T T₁ T₂ :=
  row1524_gen k534 kA6Z3 (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen.of_ctx2 ctx) h22

end Row1524Ctx

section Row1525

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall

theorem sigmaM_eq_seven_of_all_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M}
    (ctx : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.S15CtxGen G M T T₁ T₂)
    (hLifts : RowLifts G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h2 : ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
        IsLThreeOfExp 1 ↥Ls) : sigmaM G M = {7} := by
  obtain ⟨p₀, hp₀⟩ := ctx.p_mem
  have hsub : ∀ p ∈ sigmaM G M, p = 7 := by
    intro p hp
    have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
    have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
    have hp3 : p ≠ 3 := fun h => h11 (h ▸ hp)
    obtain ⟨Ls, hLs, hdvd⟩ :=
      exists_yComponent_dvd_ctx_gen kWiel_holds (kHupAt_odd hpp hp2) ctx hp
    obtain ⟨L, hL⟩ := hLifts Ls hLs
    rcases primes_of_isLThreeOfExp_one (h2 Ls L hLs hL) hpp hdvd with h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact h
  ext p
  constructor
  · intro hp
    exact hsub p hp
  · intro hp
    have : p₀ = 7 := hsub p₀ hp₀
    have hp7 : p = 7 := hp
    rw [hp7, ← this]
    exact hp₀

end Row1525

end CFSG.LocalAnalysis.RankThreeUC.S15
