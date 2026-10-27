module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDichotomy
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlockInnerAt

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique

@[expose] def KFactBlockAltFiveSectionParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockInnerNormalizerAt M S L → NineThreeTwo M S L →
    3 ∣ Nat.card (Subgroup.center ↥(barM M L)) →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ∀ φ : U →* alternatingGroup (Fin 5), Function.Surjective φ →
    (∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) →
    (∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧
        E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) ∨
      ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ blockPL M S L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 ∧
        ¬ E ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def KFactBlockAltFiveSquareParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockInnerNormalizerAt M S L → NineThreeTwo M S L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    ∀ φ : U →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5), Function.Surjective φ →
    (∀ u ∈ centralizerBar M hUM (barM M L), φ u = 1) →
    3 ≤ Open.pRank 3 (blockPL M S L)

@[expose] def KFactBlockFiveHeisParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L U : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    BlockInnerNormalizerAt M S L → NineThreeTwo M S L →
    ∀ hUM : U ≤ M, U ≤ Subgroup.normalizer (S : Set G) →
    barM M U ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
    Nat.card U = 5 ^ 3 → ¬ IsMulCommutative U → centralizerBar M hUM (barM M L) = ⊥ →
    3 ≤ Open.pRank 5 (blockPL M S L)

end CFSG.AGLEmbeddingD2
