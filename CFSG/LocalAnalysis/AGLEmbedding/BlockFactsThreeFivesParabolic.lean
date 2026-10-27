module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockThreeFivesParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L → NineThreeTwo M S L →
    ∀ (O : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (J : Fin 3 → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)),
      O ≤ blockPL M S L → blockPL M S L ≤ Subgroup.normalizer (O : Set _) →
      Nat.Coprime 5 (Nat.card O) →
      (∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), U ≤ blockPL M S L →
        ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V → IsSimpleGroup (U ⧸ V) →
          (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60) →
      (∀ i, J i ≤ blockPL M S L ∧ ∃ φ : ↥(J i) →* alternatingGroup (Fin 5),
        Function.Surjective φ ∧ ∀ x : ↥(J i), φ x = 1 ↔ (x : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ O) →
      (∀ i j, i ≠ j → ⁅J i, J j⁆ ≤ O) → 4 ≤ Open.pRank 3 (blockPL M S L)

end CFSG.AGLEmbedding
