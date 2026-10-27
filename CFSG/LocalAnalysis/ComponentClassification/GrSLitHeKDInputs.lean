module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldKDiagonalCentralStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ (a u : X) (M : Subgroup X), orderOf a = 2 → L ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) → HeldTwoA L u →
      M ≤ centralizer ({u} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))) → conjugate M a ≠ M →
      gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u →
      (∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) → False

end CFSG.ComponentClassification.GrSLit
