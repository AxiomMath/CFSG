module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618CaseDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

@[expose] def KFactRankTwoUniqueness : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X Q B U : Subgroup A),
    CFSG.IsKGroup X → CFSG.Open.pRank 3 X = 2 →
    Q ≤ X → IsPGroup 3 Q → ¬ 3 ∣ (Q.subgroupOf X).index →
    IsCyclic (Subgroup.center Q) →
    B ≤ Q → IsElemAbelian 3 B → Nat.card B = 9 →
    U ≤ Q → IsElemAbelian 3 U → Nat.card U = 9 →
    (∀ g ∈ X, B.map (MulAut.conj g).toMonoidHom ≠ U) →
    (∀ z ∈ Q, orderOf z = 3 → (∀ q ∈ Q, q * z = z * q) →
      ∀ g ∈ X, g * z * g⁻¹ ∈ B → g * z * g⁻¹ ∈ zpowers z) →
    (∃ Y : Subgroup A, Y ≤ X ∧ Y ≠ X ∧
      (∀ S : Subgroup A, S ≤ U → 1 ≤ CFSG.Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y) ∧
      (∀ S : Subgroup A, S ≤ Q → 2 ≤ CFSG.Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y)) →
    ∀ W : Subgroup A, W ≤ X → B ⊔ U ≤ normalizer (W : Set A) → Nat.Coprime (Nat.card W) 6 →
      W ≤ rankThreePrimeCore 3 X

@[expose] def KFactRankThreeStructure : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X Y Q : Subgroup A),
    CFSG.IsKGroup X →
    Q ≤ X → IsPGroup 3 Q → ¬ 3 ∣ (Q.subgroupOf X).index → 3 ≤ CFSG.Open.pRank 3 Q →
    (∃ x ∈ X, orderOf x = 3 ∧ CFSG.Open.pRank 3 (centralizer ({x} : Set A) ⊓ X) = 2) →
    Y ≤ X → Y ≠ X → Q ≤ Y →
    (∀ S : Subgroup A, S ≤ Q → 2 ≤ CFSG.Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y) →
    (∀ E : Subgroup A, E ≤ Q → IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ S : Subgroup A, S ≤ E → 1 ≤ CFSG.Open.pRank 3 S → normalizer (S : Set A) ⊓ X ≤ Y) →
    (∀ y ∈ Q, y ≠ 1 → y ^ 3 = 1 → 3 ≤ CFSG.Open.pRank 3 (centralizer ({y} : Set A) ⊓ Q) →
      centralizer ({y} : Set A) ⊓ X ≤ Y) →
    (∃ N : Subgroup A, N ≤ X ∧ (N.subgroupOf X).Normal ∧ (N.subgroupOf X).index = 3) ∧
    (∀ D : Subgroup A, D ≤ X → IsElemAbelian 3 D → Nat.card D = 9 →
      ∀ W : Subgroup A, W ≤ X → D ≤ normalizer (W : Set A) → Nat.Coprime (Nat.card W) 6 →
        W ≤ rankThreePrimeCore 3 X)

structure Setup65 (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G) :
    Prop where
  setting : Setting G
  u0 : FullCoreLocal G
  situation : SmallRankSituation G 3 P M
  solvable : Group.IsSolvable M
  wreath : Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
  point : SmallRankPoint P M x
  central : SmallRankCentral P z

@[expose] def GL83SmallRankProp65 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → Group.IsSolvable M →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ F : Subgroup G, F ≤ M → F ≠ ⊥ → Nat.Coprime (Nat.card F) 6 →
        zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

@[expose] def GL83SmallRankProp614Core20 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → Group.IsSolvable M →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H S : Subgroup G, Prop614Extremal M (zpowers x ⊔ zpowers z) H S →
        ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H →
        H = normalizer (pCoreOf 2 H : Set G) →
        IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S →
        pCoreOf 2 H ≤ S →
        (∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
          S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) →
          normalizer (S₀ : Set G) ≤ M) →
        (∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
          normalizer (S₀ : Set G) ≤ M) →
        rankThreePrimeCore 3 H ≤ M →
        rankThreePrimeCore 3 H ≤ pCoreOf 2 H →
        (∃ (K : Subgroup G) (b : G), Prop614Component M H K x z ∧
          Prop614Layer P M H K x z b) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
