module

public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def Input18_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), IsKGroup ↥X →
    ∀ p : ℕ, p.Prime → ∀ E : Subgroup G, E ≤ X → IsElemAbelian p E →
      ∀ J : Subgroup G, GLAPComponent p (X ⊓ Subgroup.centralizer (E : Set G)) J →
        ∃ 𝒞 : Set (Subgroup G), (∀ L ∈ 𝒞, GLAPComponent p X L) ∧
          (⨆ L ∈ 𝒞, L) = ⨆ g ∈ GLAPLayer p X, GLBConj g J ∧
          (∀ L ∈ 𝒞, ∀ e ∈ E, GLBConj e L ∈ 𝒞) ∧
          ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ E, GLBConj e L = L'

@[expose] def Input2_5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → ∀ X E : Subgroup Y,
    GLALayer X = X → E ≤ Subgroup.normalizer (X : Set Y) → IsElemAbelian p E →
    (∀ L L' : Subgroup Y, IsComponentOf L X → IsComponentOf L' X → ∃ e ∈ E, GLBConj e L = L') →
    (∀ e ∈ E, e ≠ 1 → ∀ L : Subgroup Y, IsComponentOf L X → GLBConj e L ≠ L) →
      (∀ X₁ : Subgroup Y, IsComponentOf X₁ X → ∃ (Z : Subgroup ↥X₁) (_ : Z.Normal),
        Z ≤ Subgroup.center ↥X₁ ∧ Nonempty (↥(GLALayer (X ⊓ Subgroup.centralizer (E : Set Y))) ≃* (↥X₁ ⧸ Z))) ∧
      X ⊓ Subgroup.centralizer (E : Set Y) =
        GLALayer (X ⊓ Subgroup.centralizer (E : Set Y)) ⊔
          ((Subgroup.center ↥X).map X.subtype ⊓ Subgroup.centralizer (E : Set Y))

@[expose] def Input14_5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → p ≠ 2 → ∀ K : Subgroup Y,
    IsQuasisimple ↥K → IsKGroup ↥K → ∀ x : Y, x ∈ Subgroup.normalizer (K : Set Y) →
      ¬ K ≤ Subgroup.centralizer ({x} : Set Y) → K ≤ Subgroup.centralizer ({x ^ p} : Set Y) →
        ∀ J : Subgroup Y, GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Y)) J →
          IsQuasisimple ↥J

@[expose] def Input25_2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K E J : Subgroup Y),
    IsQuasisimple ↥K → IsKGroup ↥K → GLAPPrimeCore 3 ↥K = ⊥ →
    E ≤ Subgroup.normalizer (K : Set Y) → IsElemAbelian 3 E → Nat.card E = 9 →
    J ≤ K ⊓ Subgroup.centralizer (E : Set Y) →
    (J.subgroupOf (K ⊓ Subgroup.centralizer (E : Set Y))).Normal →
    IsQuasisimple ↥J → IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    (∀ b ∈ E, b ≠ 1 →
      ((J ⊔ GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set Y))).subgroupOf
        (K ⊓ Subgroup.centralizer ({b} : Set Y))).Normal) →
    IsLThreeFour ↥K

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
