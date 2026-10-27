module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockOuterThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    pCoreOf 2 M ≤ S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockPLThreeSolv M S L → Open.pRank 3 M ≤ 3 →
    (∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
    (3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
      ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))

@[expose] def KFactBlockE9Transitive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    pCoreOf 2 M ≤ S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockPLThreeSolv M S L → Open.pRank 3 M ≤ 3 → 3 ≤ Open.pRank 3 L →
    Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G))) ≤ 2 →
    Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G)) →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsElemAbelian 3 E → Nat.card E = 9 →
      E ≤ barM M (Subgroup.normalizer (S : Set G)) →
      E ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ →
      ¬ TransitiveOnNonidentity (barM M (Subgroup.normalizer (S : Set G)) ⊓
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M))) E

end CFSG.LocalAnalysis.RankThreeTheoremC
