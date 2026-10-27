module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint Subgroup
open scoped MatrixGroups

@[expose] def P64IsAlt (K : Type) [Group K] : Prop :=
  ∃ (n : ℕ) (h : 5 ≤ n), Nonempty (K ≃* (TauCeti.CFSGIndex.alternating n h).Group)

@[expose] def P64IsLie (r : ℕ) (K : Type) [Group K] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex,
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧ idx.1.characteristic = r

@[expose] def P64IsSpor (s : TauCeti.SporadicName) (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group)

@[expose] def P64IsL2p2 (p : ℕ) (K : Type) [Group K] : Prop :=
  ∃ (_ : Fact p.Prime), Nonempty (K ≃* PSL(2, GaloisField p 2))

@[expose] def P64IsL3p (p : ℕ) (K : Type) [Group K] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    Nonempty (K ≃* StatedProj (StatedSL 3 F))

@[expose] def P64SporPairB (p : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (s = .Th ∧ p = 5) ∨ (s = .Co2 ∧ p = 5) ∨ (s = .Co3 ∧ p = 5) ∨ (s = .McL ∧ p = 5) ∨
    (s = .J4 ∧ p = 11)

@[expose] def P64SporPairC (p : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (s = .HS ∧ p = 5) ∨ (s = .Ru ∧ p = 5) ∨ (s = .Fi24Prime ∧ p = 7) ∨ (s = .He ∧ p = 7) ∨
    (s = .ONan ∧ p = 7) ∨ (s = .M ∧ p = 13)

@[expose] def KDI278Rank1 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z] (K : Subgroup Z), K.Normal →
    IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) → IsCatalogGroup ↥K →
      centralizer (K : Set Z) = ⊥ → (∃ P : Sylow p ↥K, Open.pRank p (P : Subgroup ↥K) ≤ 1) →
        ∀ Q : Sylow p Z, ∀ a ∈ (Q : Subgroup Z), ∀ b ∈ (Q : Subgroup Z), a ^ p = 1 → b ^ p = 1 →
          a * b = b * a

@[expose] def KDI278Alt : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z] (K : Subgroup Z), K.Normal →
    P64IsAlt ↥K → centralizer (K : Set Z) = ⊥ → Open.pRank p (⊤ : Subgroup Z) ≤ 2 →
      ∀ Q : Sylow p Z, IsMulCommutative (Q : Subgroup Z)

@[expose] def KDI278ChevP : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → P64IsLie p K → Open.pRank p (⊤ : Subgroup K) = 2 →
      P64IsL2p2 p K ∨ P64IsL3p p K ∨ P64IsU3p p K

@[expose] def KDI278L2p2 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z] (K : Subgroup Z), K.Normal →
    P64IsL2p2 p ↥K → centralizer (K : Set Z) = ⊥ →
      ∀ Q : Sylow p Z, IsMulCommutative (Q : Subgroup Z)

@[expose] def KDI278L3 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], P64IsL3p p K →
    ∀ P : Sylow p K, ∀ Y : Subgroup K,
      (∀ S : Subgroup K, S ≤ P → 2 ≤ Open.pRank p S → normalizer (S : Set K) ≤ Y) → Y = ⊤

@[expose] def KDI278ChevQ : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z] (K : Subgroup Z), K.Normal →
    IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) → (∃ r : ℕ, r ≠ p ∧ P64IsLie r ↥K) →
      centralizer (K : Set Z) = ⊥ → Open.pRank p (K : Subgroup Z) = 2 →
        Open.pRank p (⊤ : Subgroup Z) = 2 → ∀ Q : Sylow p Z,
          (∃ a ∈ (Q : Subgroup Z), ∃ b ∈ (Q : Subgroup Z), a ^ p = 1 ∧ b ^ p = 1 ∧
            a * b ≠ b * a) →
          ∀ U : Subgroup Z, U ≤ (Q : Subgroup Z) → IsElemAbelian p U → Nat.card U = p ^ 2 →
            ∀ Y : Subgroup Z,
              (∀ S : Subgroup Z, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) →
                K ≤ Y

@[expose] def KDI278Spor : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z] (K : Subgroup Z), K.Normal →
    ∀ s : TauCeti.SporadicName, P64IsSpor s ↥K → centralizer (K : Set Z) = ⊥ →
      Open.pRank p (⊤ : Subgroup Z) = 2 → ∀ Q : Sylow p Z,
        (∃ a ∈ (Q : Subgroup Z), ∃ b ∈ (Q : Subgroup Z), a ^ p = 1 ∧ b ^ p = 1 ∧
          a * b ≠ b * a) → P64SporPairB p s ∨ P64SporPairC p s

@[expose] def KDI278SporB : Prop :=
  ∀ (p : ℕ) (s : TauCeti.SporadicName), P64SporPairB p s → ∀ (Z : Type) [Group Z] [Finite Z]
    (K : Subgroup Z), K.Normal → P64IsSpor s ↥K → centralizer (K : Set Z) = ⊥ →
      Open.pRank p (⊤ : Subgroup Z) = 2 →
        (∀ a b : Z, orderOf a = p → orderOf b = p →
          ∃ g : Z, (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers b) ∨
        (∀ B U : Subgroup Z, IsElemAbelian p B → Nat.card B = p ^ 2 → IsElemAbelian p U →
          Nat.card U = p ^ 2 → ∃ g : Z, B.map (MulAut.conj g).toMonoidHom = U)

@[expose] def KDI278SporC : Prop :=
  ∀ (p : ℕ) (s : TauCeti.SporadicName), P64SporPairC p s → ∀ (Z : Type) [Group Z] [Finite Z]
    (K : Subgroup Z), K.Normal → P64IsSpor s ↥K → centralizer (K : Set Z) = ⊥ →
      ∀ B : Subgroup Z, IsElemAbelian p B → Nat.card B = p ^ 2 →
        (∀ y ∈ centralizer (B : Set Z), y ^ p = 1 → y ∈ B) →
          ∀ W : Subgroup Z, B ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) →
            W = ⊥

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
