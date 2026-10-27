module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedStructure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.CharSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.BetaBase

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.Tits.MsidePrelim

theorem d2L34BetaNormalizerSolvable_of_twoLocalSylow
    (hcov : D2L34BetaPushUpCoverSyl)
    (h1318 : D2L34BetaTwoLocalSylow) : D2L34BetaNormalizerSolvable := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax T hT C hC1 hCT hchar
  by_contra hns
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T) (C.subgroupOf T)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCT] at h1
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC1, hT.2.1.to_le hCT, rfl⟩
  have hsyl := h1318 d G P M A H R Rbar K hc hstr hAll hKmax T hT _ hloc
    (Subgroup.le_normalizer.trans hNT) hns
  obtain ⟨T₀, hT₀⟩ := exists_isSylowTwoOf (H ⊓ M)
  have hT₀M := (D2L34BetaConf.isSylowTwoOf_of_cover hcov hc hstr hAll.onlyL34At hT₀).1
  obtain ⟨x, -, hxN, hxM, k, hk⟩ := D2L34BetaConf.exists_two_element hc hT₀
  have hxT₀ : x ∉ T₀ := fun h => hxM ((hT₀.1.trans inf_le_right) h)
  have hlt : T₀ < Subgroup.zpowers x ⊔ T₀ :=
    lt_of_le_of_ne le_sup_right fun h => hxT₀ (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hcard : Nat.card T < Nat.card (Subgroup.zpowers x ⊔ T₀ : Subgroup G) := by
    rw [card_eq_of_isSylowTwoOf hT hT₀M]
    exact Subgroup.card_lt_of_lt hlt
  exact not_isSylowTwoOf_of_card_lt hT.2.1 (isPGroup_zpowers_sup hT₀.2.1 hxN hk) hcard hNT hsyl

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
