module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

@[expose] def Prop63Out (B M₀ : Subgroup G) : Prop :=
  GLBCore 3 3 B ≤ M₀ ∧ Even (Nat.card (GLAPPrimeCoreOf 3 M₀))

@[expose] def Prop67Out (B : Subgroup G) : Prop :=
  ∀ x ∈ B, x ≠ 1 → ∀ K : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K →
    ¬ IsStronglyLocallyOneBalanced 3 B x K → ¬ K ≤ GLBCore 3 3 B → IsHSet B K

@[expose] noncomputable def kZeroOf (B K : Subgroup G) : Subgroup G :=
  GLAPLayer 3 (K ⊓ Subgroup.centralizer (centralizerQuot B K : Set G))

structure IsIaFacts (B K : Subgroup G) (a : G) : Prop where
  component : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) (bClosureIa K a)
  normal : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (bClosureIa K a : Set G)
  lThreeFour : IsLThreeFour (↥(bClosureIa K a) ⧸ GLAPPrimeCore 3 ↥(bClosureIa K a))
  kZero_le : kZeroOf B K ≤ bClosureIa K a
  le_kZero_sup : bClosureIa K a ≤ kZeroOf B K ⊔ GLAPPrimeCoreOf 3 (bClosureIa K a)

structure IsProp68Facts (B K : Subgroup G) : Prop where
  normalizes : B ≤ Subgroup.normalizer (K : Set G)
  lThreeFour : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)
  aK : IsEkIn 3 2 B (centralizerQuot B K)
  fK : IsEkIn 3 2 B (B ⊓ K)
  sup_eq : centralizerQuot B K ⊔ (B ⊓ K) = B
  inf_eq : centralizerQuot B K ⊓ (B ⊓ K) = ⊥
  ia : ∀ a ∈ centralizerQuot B K, a ≠ 1 → IsIaFacts B K a

@[expose] def Prop68Out (B : Subgroup G) : Prop :=
  ∀ K : Subgroup G, IsHSet B K → IsProp68Facts B K

@[expose] def UniqComp (B : Subgroup G) : Prop :=
  ∀ x ∈ B, x ≠ 1 → ∀ I K : Subgroup G,
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) I →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) K →
    B ≤ Subgroup.normalizer (I : Set G) → B ≤ Subgroup.normalizer (K : Set G) →
    IsLThreeFour (↥I ⧸ GLAPPrimeCore 3 ↥I) → IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) →
    IsEkIn 3 2 B (B ⊓ K) → I = K

@[expose] def Lemma75Stmt (B : Subgroup G) : Prop :=
  ∀ K : Subgroup G, IsHSet B K → ∀ N : Subgroup G, N ≠ ⊤ → B ≤ N → Covers3 N K →
    IsComponentOf (barX 3 N (GLAPLayer 3 (K ⊓ N))) ⊤

@[expose] def Lemma76Stmt (B : Subgroup G) : Prop :=
  ∀ K : Subgroup G, IsHSet B K → ∀ N : Subgroup G, N ≠ ⊤ → K ⊔ gammaOneThree B ≤ N →
    ∀ I : Subgroup G, GLAPComponent 3 N I → barX 3 N I = barX 3 N K →
      Even (Nat.card (⁅I, GLAPPrimeCoreOf 3 N⁆ : Subgroup G))

@[expose] def Case1Hyp (B : Subgroup G) : Prop :=
  ∀ K₁ K₂ : Subgroup G, IsHSet B K₁ → IsHSet B K₂ →
    centralizerQuot B K₁ = centralizerQuot B K₂

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
