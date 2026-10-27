module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding

@[expose] def KFactBlockHeisenbergAut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    pCoreOf 2 M ≤ S → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card ↥(barM M L) →
      ¬ p ∣ ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L)).index →
      ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ →
        Nat.card E = p ^ 3 → (∀ x ∈ E, x ^ p = 1) → (∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
