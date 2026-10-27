module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

@[expose] def KFactBlockFieldIndexAt (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    pCoreOf 2 M ≤ S → (L.subgroupOf M).Normal →
    (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) →
    p ∣ Nat.card (perfectJoin (blockPL M S L)) →
    Open.pRank p (perfectJoin (blockPL M S L)) ≤ 1 →
    ∀ a : ↥M ⧸ CFSG.pCore 2 ↥M, IsPGroup p (Subgroup.zpowers a) →
      a ∈ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (¬ ∃ v ∈ perfectJoin (blockPL M S L), ∀ w ∈ perfectJoin (blockPL M S L),
        ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin (blockPL M S L))) →
      ∃ N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), N.Normal ∧ N.index = p

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoAlphaR (p : ℕ) (M H R : Subgroup G) : Prop :=
  ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ (L.subgroupOf M).Normal ∧
    p ∣ Nat.card (perfectJoin (blockPL M (pCoreOf 2 H) L)) ∧
    ∃ a : ↥M, (a : G) ∈ R ∧
      ¬ ∃ v ∈ perfectJoin (blockPL M (pCoreOf 2 H) L),
        ∀ w ∈ perfectJoin (blockPL M (pCoreOf 2 H) L),
          ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M) a * v, w⁆ ∈
            pCoreOf 2 (perfectJoin (blockPL M (pCoreOf 2 H) L))

end CFSG.LocalAnalysis.RankThreeTheoremC
