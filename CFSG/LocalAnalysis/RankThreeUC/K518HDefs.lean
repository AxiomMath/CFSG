module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding

@[expose] def K518Crit : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L S P : Subgroup Y), CFSG.Open.IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → ¬ RankOneChevTwo (↥L ⧸ Subgroup.center ↥L) →
    CFSG.QuasithinUnique.IsSylowTwoOf S L → IsMinOverBorel L S P → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card (Subgroup.center ↥L) →
    ∀ r : Y, r ∈ Subgroup.normalizer (L : Set Y) → r ∈ Subgroup.normalizer (S : Set Y) →
      (∃ k : ℕ, orderOf r = p ^ k) → r ∉ L ⊔ Subgroup.centralizer (L : Set Y) →
      r ^ p ∈ L ⊔ Subgroup.centralizer (L : Set Y) → r ^ p ∉ Subgroup.centralizer (L : Set Y) →
      2 ≤ CFSG.Open.pRank p (pElementSubgroup 2 P ⊔ Subgroup.zpowers r)

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
