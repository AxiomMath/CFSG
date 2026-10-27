module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

section Defs

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def jLayerOf (L A : Subgroup G) : Subgroup G :=
  GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G))

@[expose] noncomputable def kOf (L A : Subgroup G) (x : G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)), GLBConj g (jLayerOf L A)

end Defs

@[expose] def IsLThreeEps (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧
      Nonempty (Y ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      Nonempty (Y ≃* StatedProj (StatedSU 3 q K)))

@[expose] def Input30_2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsLThreeEps (K ⧸ GLAPPrimeCore 3 K) →
    (∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9) ∧
    ∀ F : Subgroup K, IsElemAbelian 3 F → Nat.card F = 9 →
      (∀ x ∈ F, x ≠ 1 → ∀ y ∈ F, y ≠ 1 → ∃ g : K, g * x * g⁻¹ = y) →
      ∀ P : Subgroup K, IsPGroup 3 P → P ≤ Subgroup.centralizer (F : Set K) → F ≤ P → P ≤ F

@[expose] def InputKType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ (b : G) (L A : Subgroup G), IsExtremalWitness B b L A →
      ∀ x ∈ A, x ≠ 1 → IsLThreeEps (barOf 3 (kOf L A x))

@[expose] def InputJNormalA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBOneMax 3 B → ∀ (b : G) (L A : Subgroup G), IsExtremalWitness B b L A →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (jLayerOf L A : Set G)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
