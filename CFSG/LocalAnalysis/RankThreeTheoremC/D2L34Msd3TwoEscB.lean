module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.E81
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]

theorem D2L34BetaConf3.false_of_two_escapes
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hAll : D2L34AllResidue3 P M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) {X₁ X₂ W₁ W₂ : Subgroup G}
    (hX₁ : X₁ ≠ ⊥) (hX₁2 : IsPGroup 2 X₁)
    (hX₁T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₁ : Set G))
    (hX₂ : X₂ ≠ ⊥) (hX₂2 : IsPGroup 2 X₂)
    (hX₂T : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (X₂ : Set G))
    (hW₁ : W₁ ≤ M ⊓ Subgroup.normalizer (X₁ : Set G))
    (hW₂ : W₂ ≤ M ⊓ Subgroup.normalizer (X₂ : Set G))
    (hW₁p : IsPGroup 3 W₁) (hW₂p : IsPGroup 3 W₂) (hW₁c : ¬ IsCyclic W₁) (hW₂c : ¬ IsCyclic W₂)
    (hW : IsPGroup 3 (W₁ ⊔ W₂ : Subgroup G)) (h9 : 9 < Nat.card (W₁ ⊔ W₂ : Subgroup G)) :
    False :=
  D2L34BetaConf3.false_of_two_escapes_of_residue hc hstr hAll hAll.onlyL34At hT hNT hX₁ hX₁2 hX₁T
    hX₂ hX₂2 hX₂T hW₁ hW₂ hW₁p hW₂p hW₁c hW₂c hW h9

end CFSG.LocalAnalysis.RankThreeTheoremC
