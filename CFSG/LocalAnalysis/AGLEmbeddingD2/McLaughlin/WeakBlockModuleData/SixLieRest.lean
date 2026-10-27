module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieClauseO

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def KFactBlockSixLieHP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeTwo M S L → BlockPLThreeSolv M S L →
    IsFiveList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) →
    Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≤ 2 →
      ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → IsPGroup 3 T → IsElemAbelian 3 T

@[expose] def KFactBlockSixLieNoSwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeTwo M S L → BlockPLThreeSolv M S L →
    IsFiveList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsElemAbelian 3 E → Nat.card E = 9 →
      E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      (∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → IsPGroup 3 T → Nat.card T ≤ 9) →
      ¬ IrreducibleOn
        (Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
          Subgroup.normalizer
            (barM M (Subgroup.normalizer (S : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
          Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) E

theorem kFactBlockSixLie_of_parts (hP : KFactBlockSixLieHP) (hN : KFactBlockSixLieNoSwap) :
    KFactBlockSixLie := by
  intro G _ _ M S L hK hAsc hL h2 hsolv hF
  exact ⟨clauseO_of_isFiveList hL hF, hP G M S L hK hAsc hL h2 hsolv hF,
    hN G M S L hK hAsc hL h2 hsolv hF⟩

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
