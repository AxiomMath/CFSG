module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

@[expose] def gammaQ {X : Type} [Group X] [Finite X] (Q : Subgroup X) : Subgroup X :=
  (⨆ (S : Subgroup X) (_ : S ≤ Q ∧ 2 ≤ CFSG.Open.pRank 3 S), normalizer (S : Set X)) ⊔
    ⨆ (S : Subgroup X) (_ : ∃ E : Subgroup X, E ≤ Q ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        S ≤ E ∧ S ≠ ⊥), normalizer (S : Set X)

@[expose] def KFactRankThreeCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    primeComplementCore (G := X) 3 = ⊥ →
    ∀ L : Subgroup X, L.Normal → IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
      centralizer (L : Set X) = ⊥ →
    ∀ Q : Sylow 3 X, 3 ≤ CFSG.Open.pRank 3 (Q : Subgroup X) →
    (∃ x : X, orderOf x = 3 ∧ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2) →
    ¬ L ≤ gammaQ (Q : Subgroup X) →
    Nonempty (L ≃* PSL(2, GaloisField 3 3)) ∧ (L.index = 3 ∨ L.index = 6)

structure K2Setup (G : Type) [Group G] [Finite G] (Y Q : Subgroup G) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections G
  pgroup : IsPGroup 3 Q
  index : ¬ 3 ∣ Q.index
  rank : 3 ≤ CFSG.Open.pRank 3 Q
  elt : ∃ x : G, orderOf x = 3 ∧ CFSG.Open.pRank 3 (centralizer ({x} : Set G)) = 2
  proper : Y ≠ ⊤
  le : Q ≤ Y
  y1 : ∀ S : Subgroup G, S ≤ Q → 2 ≤ CFSG.Open.pRank 3 S → normalizer (S : Set G) ≤ Y
  y2 : ∀ E : Subgroup G, E ≤ Q → IsElemAbelian 3 E → Nat.card E = 27 →
    ∀ S : Subgroup G, S ≤ E → 1 ≤ CFSG.Open.pRank 3 S → normalizer (S : Set G) ≤ Y

@[expose] def K2Concl (G : Type) [Group G] [Finite G] : Prop :=
  (∃ N : Subgroup G, N.Normal ∧ N.index = 3) ∧
    ∀ D : Subgroup G, IsElemAbelian 3 D → Nat.card D = 9 →
      ∀ W : Subgroup G, D ≤ normalizer (W : Set G) → Nat.Coprime (Nat.card W) 6 →
        W ≤ primeComplementCore (G := G) 3

@[expose] def K2Grp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y Q : Subgroup G), K2Setup G Y Q → K2Concl G

abbrev Bar (G : Type) [Group G] : Type := G ⧸ primeComplementCore (G := G) 3

abbrev barMk (G : Type) [Group G] : G →* Bar G :=
  QuotientGroup.mk' (primeComplementCore (G := G) 3)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
