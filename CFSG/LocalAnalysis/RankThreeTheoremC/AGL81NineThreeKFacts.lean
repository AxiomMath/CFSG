module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeList

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsThreeOneIndex (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  IsNineThreeIndex p i ∨ (p = 5 ∧ i = .sporadic .Fi22) ∨
    ∃ (n : ℕ) (hn : 5 ≤ n), i = .alternating n hn ∧ (n = 2 * p ∨ n = 3 * p)

@[expose] def KFactThreeOne : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (X K P E : Subgroup Y), p.Prime → p ≠ 2 →
    K ≤ X → X ≤ Subgroup.normalizer (K : Set Y) → CFSG.Open.IsQuasisimple K → CFSG.IsKGroup K →
    primeComplementCore (G := K) p = ⊥ → 2 ≤ CFSG.Open.pRank p X →
    CFSG.Quasithin.IsSylowIn p P X → E ≤ P → IsElemAbelian p E → Nat.card E = p ^ 2 →
    ¬ K ≤ (if 3 ≤ CFSG.Open.pRank p P then GLBWeakCore p P else GLBCore p 1 E) →
    (∃ i : TauCeti.CFSGIndex, IsThreeOneIndex p i ∧ Nonempty (K ≃* i.Group)) ∧
      Subgroup.center K = ⊥

@[expose] def KFactSevenFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.evenRank G = 3 → ∀ (p : ℕ) (i : TauCeti.CFSGIndex),
    ((7 ≤ p ∧ ∃ hn, i = .alternating (2 * p) hn) ∨ (5 ≤ p ∧ ∃ hn, i = .alternating (3 * p) hn) ∨
      (p = 5 ∧ i = .sporadic .Fi22)) → IsSimpleGroup i.Group →
    ∀ (H : Subgroup G) (φ : H →* i.Group), Function.Surjective φ → False

@[expose] def KFactNineThreeOutPClosed : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), p.Prime → p ≠ 2 → K.Normal →
    NineThreeListGroup p K → ∀ R : Sylow p Y,
      ((R : Subgroup Y) ⊔ (K ⊔ Subgroup.centralizer (K : Set Y))).Normal

@[expose] def KFactNineThreeRankTwo : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), p.Prime →
    (∃ i : TauCeti.CFSGIndex, IsNineThreeIndex p i ∧ Nonempty (K ≃* i.Group)) →
    CFSG.Open.pRank p K ≤ 1 →
    ∃ d : TauCeti.ValidLieTypeIndex, IsNineThreeProductIndex p d ∧
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
