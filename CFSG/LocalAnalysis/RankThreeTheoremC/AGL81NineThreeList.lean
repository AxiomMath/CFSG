module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G] {p : ℕ}

@[expose] def IsNineThreeLieIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q) ∨
  (∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q) ∨
  IsSpFourIndex p d ∨
  (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q) ∨
  (p = 3 ∧ ∃ m : ℕ, d.1 = .reeG2 m) ∨
  (p = 3 ∧ ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧
      (d.1 = .A 1 q ∨ d.1 = .G2 q ∨ d.1 = .B 2 q)) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) ∨ d.1 = .tits)) ∨
  (p = 5 ∧ (d.1 = .suzuki 2 ∨ d.1 = .tits ∨ d.1 = .reeF4 2))

@[expose] def IsNineThreeIndex (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .cyclic _ _ => False
  | .alternating n _ => (p = 3 ∧ (n = 6 ∨ n = 9)) ∨ (p = 5 ∧ n = 10)
  | .lie d => IsNineThreeLieIndex p d
  | .sporadic s => (p = 3 ∧ (s = .M11 ∨ s = .M12 ∨ s = .J3)) ∨
      (p = 5 ∧ (s = .McL ∨ s = .HS ∨ s = .Ru)) ∨
      (p = 7 ∧ (s = .ONan ∨ s = .Fi24Prime ∨ s = .He)) ∨ (p = 11 ∧ s = .J4)

@[expose] def IsNineThreeProductIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
  (p = 5 ∧ d.1 = .suzuki 2)

@[expose] def NineThreeListGroup (p : ℕ) (K : Type*) [Group K] : Prop :=
  (∃ i : TauCeti.CFSGIndex, IsNineThreeIndex p i ∧ Nonempty (K ≃* i.Group)) ∨
  ∃ d : TauCeti.ValidLieTypeIndex, IsNineThreeProductIndex p d ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group × (TauCeti.CFSGIndex.lie d).Group)

@[expose] def NineThreeListAt (p : ℕ) (M N : Subgroup G) : Prop :=
  d1KBar p M N ≠ ⊥ → NineThreeListGroup p (d1KBar p M N)

@[expose] def Hyp917OneAt (p : ℕ) (M H N : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∃ W : Subgroup G, ∃ _ : W ≤ H ⊓ N,
    (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K ∧
    (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) p)) ≤ d1KBar p M N

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
