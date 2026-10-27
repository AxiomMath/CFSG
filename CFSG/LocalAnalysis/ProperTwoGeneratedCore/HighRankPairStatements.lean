module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyGeneration

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped MatrixGroups

universe u

variable {G : Type u} [Group G]

@[expose] def SmallerR1Full (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
    2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K

@[expose] def PairGenerationTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    BasePointPairGeneration H z

@[expose] def pointRoots (H : Subgroup G) (z u : G) : Set G :=
  conjugacyWithin H z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)

@[expose] def distinguishedRoots (H : Subgroup G) (z w : G) : Set G :=
  involutionPointClass z ∩ (H : Set G) ∩ (Subgroup.centralizer ({w} : Set G) : Set G)

@[expose] def FieldInvolutionOn (L : Subgroup G) (v : G) (a : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ (2 * a) ∧
    ∃ φ : L ≃* SL(2, F), ∀ x y : L, (y : G) = v * x * v⁻¹ → ∀ i j,
      (φ y : Matrix (Fin 2) (Fin 2) F) i j = (φ x : Matrix (Fin 2) (Fin 2) F) i j ^ 2 ^ a

@[expose] def NonInnerOn (L : Subgroup G) (v : G) : Prop :=
  ¬ ∃ g ∈ L, ∀ x ∈ L, v * x * v⁻¹ = g * x * g⁻¹

@[expose] def SubfieldCentralizer (L : Subgroup G) (v : G) (a : ℕ) : Prop :=
  ∃ (k : Type) (_ : Field k), Nat.card k = 2 ^ a ∧
    Nonempty ((L ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) ≃* SL(2, k))

@[expose] def SquareFieldAction (H : Subgroup G) (z u v : G) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ FieldInvolutionOn (localInvolutionPointHull z u) v a ∧
    SubfieldCentralizer (localInvolutionPointHull z u) v a ∧
    Nat.card (pointRoots H z u) = 2 ^ (2 * a) - 1 ∧
    Nat.card (pointRoots H z u ∩ (Subgroup.centralizer ({v} : Set G) : Set G) : Set G) =
      2 ^ a - 1

@[expose] def NoncentralPairActionAt (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) : Prop :=
  ∀ u v : G, u ∈ pairPointStabilizer H beta → orderOf u = 2 → Commute u z → Commute u t →
    v ∈ pairPointStabilizer H beta → orderOf v = 2 → Commute u v →
    (∃ x ∈ pointRoots H z u, ¬ Commute v x) → SquareFieldAction H z u v

@[expose] def NoncentralPairActionTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, NoncentralPairActionAt H z beta t

@[expose] def WitnessPrimeData (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t u v s r : G) (a p : ℕ) : Prop :=
  ∃ A : Subgroup G, A ≤ pairOddCore H beta ∧
    u ∈ Subgroup.normalizer (A : Set G) ∧ v ∈ Subgroup.normalizer (A : Set G) ∧
    t ∈ Subgroup.normalizer (A : Set G) ∧ IsPGroup p A ∧ ¬ IsCyclic A ∧
    ⁅A, Subgroup.zpowers t⁆ = A ∧
    (A ⊓ Subgroup.centralizer ({t} : Set G)).relIndex A =
      (p ^ (Nat.factorization (2 ^ a + 1) p)) ^ 2 ∧
    A ≤ Subgroup.centralizer ({s} : Set G) ∧ ¬ A ≤ Subgroup.centralizer ({r} : Set G) ∧
    (∀ γ : rightCosetSpace H, rightCosetTranslate H γ t = γ →
      ∃ x ∈ A, rightCosetTranslate H γ x ≠ γ) ∧
    A ≤ localInvolutionPointHull z s

@[expose] def HighRankPairWitness (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) [Finite G] : Prop :=
  ∃ z₀ u v : G, ∃ a ε : ℕ, 1 ≤ a ∧ (ε = 2 ∨ ε = 3) ∧ z₀ ∈ conjugacyWithin H z ∧
    u ∈ pairPointStabilizer H beta ∧ v ∈ pairPointStabilizer H beta ∧
    orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v ∧ Commute u v ∧
    Commute u z₀ ∧ Commute v z₀ ∧ Commute u t ∧ Commute v t ∧
    FieldInvolutionOn (localInvolutionPointHull z u) v a ∧
    NonInnerOn (localInvolutionPointHull z u) v ∧
    FieldInvolutionOn (localInvolutionPointHull z v) u a ∧
    NonInnerOn (localInvolutionPointHull z v) u ∧
    Nat.card (distinguishedRoots H z u) = 2 ^ (2 * a) - 1 ∧
    Nat.card (distinguishedRoots H z v) = 2 ^ (2 * a) - 1 ∧
    Nat.card (distinguishedRoots H z u ∩ distinguishedRoots H z v : Set G) = 2 ^ a - 1 ∧
    Nat.card (conjugacyWithin H z) = (2 ^ a - 1) * (2 ^ a + 1) ^ ε ∧
    (ε = 2 → distinguishedRoots H z (u * v) =
      distinguishedRoots H z u ∩ distinguishedRoots H z v) ∧
    (ε = 3 → Nat.card (distinguishedRoots H z (u * v)) = 2 ^ (2 * a) - 1 ∧
      ∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ (2 * a) ∧
        Nonempty (localInvolutionPointHull z (u * v) ≃* SL(2, F))) ∧
    ∃ s r : G, (ε = 2 ∧ s = u * v * t ∧ r = u ∨ ε = 3 ∧ s = u * t ∧ r = v) ∧
      orderOf s = 2 ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ a + 1 → WitnessPrimeData H z beta t u v s r a p) ∧
      ∀ γ : rightCosetSpace H, rightCosetTranslate H γ t = γ →
        ¬ Subgroup.centralizer ({s} : Set G) ≤ rightCosetStabilizer H γ ∧
        localInvolutionPointHull z r ⊓ Subgroup.centralizer ({s} : Set G) ≤
          localInvolutionPointHull z s ∧
        SubfieldCentralizer (localInvolutionPointHull z r) s a ∧
        Nat.card (involutionPointClass z ∩ (rightCosetStabilizer H γ : Set G) ∩
          (Subgroup.centralizer ({r} : Set G) : Set G) ∩
          (Subgroup.centralizer ({s} : Set G) : Set G) : Set G) = 2 ^ a - 1 ∧
        (4 ≤ 2 ^ a → 2 ≤ twoRank (localInvolutionPointHull z s))

@[expose] def HighRankPairWitnessTheorem (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, 2 ≤ twoRank (pairPointStabilizer H beta) →
        HighRankPairWitness H z beta t

@[expose] def SuzukiOuterOdd : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    Odd (MulAut.conj : CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m →*
      MulAut (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)).range.index

end CFSG.ProperTwoGeneratedCore.HighRankPair
