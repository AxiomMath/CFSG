module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PrimeBlocksD2

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

variable {G : Type} [Group G]

@[expose] def BlockInnerNormalizerAt (M S L : Subgroup G) : Prop :=
  ∀ l ∈ barM M L, (∀ s ∈ barM M S, ∃ s' ∈ barM M S, ∀ y ∈ barM M L,
      (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) →
    l ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L)

theorem AGLPair.blockInnerNormalizerAt [Finite G] {p : ℕ} {M H R L : Subgroup G}
    (h : AGLPair p M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : BlockInnerNormalizerAt M (pCoreOf 2 H) L :=
  fun l hl hlS => h.blockInnerNormalizer h84 h86 hD2 hL l hl hlS

end CFSG.AGLEmbeddingD2
