module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldKDiagonalStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ (a u : X) (M : Subgroup X), orderOf a = 2 → L ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) → HeldTwoA L u →
      M ≤ centralizer ({u} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))) → conjugate M a ≠ M →
      gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u →
      (¬ M ⊓ (conjugate M a ⊔ (pPrimeCore 2 ↥(centralizer ({u} : Set X))).map
          (centralizer ({u} : Set X)).subtype) ≤
          (pPrimeCore 2 ↥(centralizer ({u} : Set X))).map (centralizer ({u} : Set X)).subtype ∨
        ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) → False

@[expose] def HeldKNormalFromComponent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ u : X, HeldTwoA L u →
      IsComponent ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))) →
      ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).Normal ∧
      ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({u} : Set X) →
        (K₁.subgroupOf (centralizer ({u} : Set X))).Normal →
        Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u)) → K₁ = gsFixedLayer L u

end CFSG.ComponentClassification.GrSLit
