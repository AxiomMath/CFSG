module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

@[expose] def KFactBlockFieldIndex : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    pCoreOf 2 M ≤ S → (L.subgroupOf M).Normal →
    (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q (barM M L) ≤ 3) →
    3 ∣ Nat.card (perfectJoin (blockPL M S L)) →
    Open.pRank 3 (perfectJoin (blockPL M S L)) ≤ 1 →
    ∀ a : ↥M ⧸ CFSG.pCore 2 ↥M, IsPGroup 3 (Subgroup.zpowers a) →
      a ∈ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (¬ ∃ v ∈ perfectJoin (blockPL M S L), ∀ w ∈ perfectJoin (blockPL M S L),
        ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin (blockPL M S L))) →
      ∃ N : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), N.Normal ∧ N.index = 3

variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoAlpha (p : ℕ) (P : Sylow p G) (M H : Subgroup G) : Prop :=
  ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ (L.subgroupOf M).Normal ∧
    p ∣ Nat.card (perfectJoin (blockPL M (pCoreOf 2 H) L)) ∧
    ∃ a : ↥M, (a : G) ∈ (P : Subgroup G) ∧
      ¬ ∃ v ∈ perfectJoin (blockPL M (pCoreOf 2 H) L),
        ∀ w ∈ perfectJoin (blockPL M (pCoreOf 2 H) L),
          ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M) a * v, w⁆ ∈
            pCoreOf 2 (perfectJoin (blockPL M (pCoreOf 2 H) L))

@[expose] def D1CaseTwoCentral3Beta (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    ∀ z : H, D1CaseTwoCand p M H R z →
      (∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)) →
      ¬ (p = 3 ∧ R = (P : Subgroup G) ∧ D1CaseTwoAlpha p P M H) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
