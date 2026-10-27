module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

@[expose] def D3AbelianSix : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∃ A : Subgroup (D4Model K), IsElemAbelian 3 A ∧ 3 ^ (6 * n) ≤ Nat.card A

@[expose] def D3TwoLocalFour : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∃ (F : Subgroup (D4Model K)) (z : D4Model K), IsElemAbelian 3 F ∧ 3 ^ (4 * n) ≤ Nat.card F ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ s ∈ F, s * z = z * s

@[expose] def D3TrialityCentRank : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ t : MulAut (D4Model K), t ^ 3 = 1 → t ∉ D4Img K →
      ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → (∀ a ∈ A, t a = a) →
        Nat.card A ≤ 3 ^ (4 * n)

@[expose] def D3InnerInvolution : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ t : MulAut (D4Model K), t ^ 3 = 1 → t ∉ D4Img K →
      ∀ z : MulAut (D4Model K), z ^ 2 = 1 → z ≠ 1 →
        z ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (D4Model K) → z * t = t * z →
        ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → (∀ a ∈ A, t a = a) → (∀ a ∈ A, z a = a) →
          Nat.card A ≤ 3 ^ (2 * n)

@[expose] def D3FieldInvolution : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ t : MulAut (D4Model K), t ^ 3 = 1 → t ∉ D4Img K →
      ∀ z : MulAut (D4Model K), z ^ 2 = 1 →
        z ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (D4Model K) → z * t = t * z →
        ∀ A : Subgroup (D4Model K), IsElemAbelian 3 A → (∀ a ∈ A, t a = a) → (∀ a ∈ A, z a = a) →
          Nat.card A ≤ 3 ^ (2 * n)

@[expose] def D3FixedPointFree : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ E : Subgroup (MulAut (D4Model K)), IsElemAbelian 3 E → ¬ E ≤ D4Img K →
      3 ^ (4 * n) ≤ Nat.card E →
      ∀ T : Subgroup (MulAut (D4Model K)), T ≠ ⊥ → IsPGroup 2 T →
        E ≤ Subgroup.normalizer (T : Set (MulAut (D4Model K))) →
        (∀ x ∈ T, (∀ e ∈ E, e * x = x * e) → x = 1) → False

@[expose] def D3TwoLocalTriality : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), Nat.card K = 3 ^ n →
    ∀ E : Subgroup (MulAut (D4Model K)), IsElemAbelian 3 E → ¬ E ≤ D4Img K →
      3 ^ (4 * n) ≤ Nat.card E →
      ∀ T : Subgroup (MulAut (D4Model K)), T ≠ ⊥ → IsPGroup 2 T →
        E ≤ Subgroup.normalizer (T : Set (MulAut (D4Model K))) → False

end CFSG.LocalAnalysis.GLTheoremA
