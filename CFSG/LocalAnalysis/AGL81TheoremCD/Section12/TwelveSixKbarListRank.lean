module

import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.NineSettingOfHypC
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem pRank_three_le_of_mem_H2Fam (h : NineSettingGen G M p Q H E k) (hH2 : H ∈ H2Fam M Q)
    (hp : p ∉ sigmaM G M) (h2 : 2 ≤ CFSG.Open.pRank 3 (H ⊓ M)) :
    CFSG.Open.pRank 3 H ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTne : CFSG.pCore 2 ↥H ≠ ⊥ := by
    intro hbot
    have hpcof : pCoreOf 2 H = ⊥ := by
      rw [pCoreOf, hbot, Subgroup.map_bot]
    have hcen : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (bot_le : (⊥ : Subgroup G) ≤ Subgroup.center G)
    have hcl := hH2.2.2.2
    rw [hpcof, hcen, inf_top_eq] at hcl
    exact h.not_le (hcl.trans bot_le)
  have hO : pCoreOf 2 H ≠ ⊥ := by
    intro hbot
    exact hTne ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hbot)
  have htop : IsTwoLocal (⊤ : Subgroup ↥H) := by
    refine ⟨CFSG.pCore 2 ↥H, hTne, CFSG.pCore_isPGroup, ?_⟩
    exact (show ⊤ = Subgroup.normalizer ((CFSG.pCore 2 ↥H : Subgroup ↥H) : Set ↥H) from by
      rw [Subgroup.normalizer_eq_top])
  have hle : CFSG.Open.pRank 3 H ≤ rankThreeLocalRank 3 H :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) H).le.trans
      (local_pRank_le_localRank (G := ↥H) 3 (by norm_num) (⊤ : Subgroup ↥H) htop)
  have hloc : rankThreeLocalRank 3 H ≤ 3 := by
    by_contra hlt
    have := (h.nineFiveGen hp).2.2 (Or.inl hO) (by omega)
    omega
  exact hle.trans hloc

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKCtx.three_le_pRank_inf (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) : 3 ≤ CFSG.Open.pRank 3 (H ⊓ M) :=
  CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (D.V_le.trans (D.sup_le hc.data)) D.cfg.elem
    (k := 3) (by rw [D.cfg.card]; norm_num)

theorem TwelveSixKCtx.pRank_three_le (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) : CFSG.Open.pRank 3 H ≤ 3 := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hd := hc.ctx.hypCGen hEQ hE hEc hΓ
  exact hd.toNineSettingGen.pRank_three_le_of_mem_H2Fam hd.mem_H2Fam hd.not_mem_sigmaM
    ((by norm_num : 2 ≤ 3).trans (hc.three_le_pRank_inf D))

theorem TwelveSixKCtx.pRank_le_three (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) :
    CFSG.Open.pRank p H ≤ 3 := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  have hd := hc.ctx.hypCGen hEQ hE hEc hΓ
  exact (hd.toNineSettingGen.pRank_le_of_mem_H2Fam hd.mem_H2Fam hd.not_mem_sigmaM).1

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
