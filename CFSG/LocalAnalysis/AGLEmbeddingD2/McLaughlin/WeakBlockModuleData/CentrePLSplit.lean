module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentrePL

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactBlockCentreNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeConclusion M S L → ¬ NineThreeOne L →
    (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) → BlockPLThreeSolv M S L →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)

@[expose] def KFactBlockCentreRankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeConclusion M S L → ¬ NineThreeOne L →
    (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) → BlockPLThreeSolv M S L →
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    2 ≤ Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L))

theorem kFactBlockCentrePLRank_of_parts (ha : KFactBlockCentreNine)
    (hb : KFactBlockCentreRankTwo) : KFactBlockCentrePLRank := by
  intro G _ _ M S L hL hconc hnot hSyl hsolv hZP hZ
  have h9 := ha G M S L hL hconc hnot hSyl hsolv hZ
  exact ⟨h9, hb G M S L hL hconc hnot hSyl hsolv hZP hZ h9⟩

end CFSG.AGLEmbeddingD2.McLaughlin
