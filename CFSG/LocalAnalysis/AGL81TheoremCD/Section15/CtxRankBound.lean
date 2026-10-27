module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem S15CtxGen.pRank_three_normalizer_le_three {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) (hM3 : 2 ≤ CFSG.Open.pRank 3 M) {C : Subgroup G}
    (hC : C ≠ ⊥) (hCT : C ≤ T) (hchar : (C.subgroupOf T).Characteristic) :
    CFSG.Open.pRank 3 (Subgroup.normalizer (C : Set G)) ≤ 3 := by
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC, ctx.sylow.isPGroup.to_le hCT, rfl⟩
  by_cases h3 : (3 : ℕ) ∈ CFSG.Open.rankThreeSigmaA G
  · have h3s : 3 ∈ sigmaSet G M := ⟨h3, hM3⟩
    exact (ctx.rank_char 3 h3s C hC hCT hchar).trans (by norm_num)
  · exact ctx.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num) h3 hloc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
