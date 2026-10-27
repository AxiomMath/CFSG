module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

variable {X : Type} [Group X]

@[expose] def KFact518Out : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L N S P : Subgroup Y), CFSG.Open.IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → ¬ RankOneChevTwo (↥L ⧸ Subgroup.center ↥L) →
    N ≤ Subgroup.normalizer (L : Set Y) → CFSG.QuasithinUnique.IsSylowTwoOf S L →
    IsMinOverBorel L S P → pElementSubgroup 2 P ≤ N → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.center ↥L) → p ∣ Nat.card ↥(N ⊓ L) → CFSG.Open.pRank p N ≤ 1 →
      ∀ x ∈ N, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ L ⊔ Subgroup.centralizer (L : Set Y)

end CFSG.LocalAnalysis.RankThreeUC.S15
