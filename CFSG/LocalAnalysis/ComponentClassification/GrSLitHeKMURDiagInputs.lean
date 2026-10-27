module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

@[expose] def HeldKDiagonalPumpUpDiagonalResidue : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), HeldEndSetting X L →
    ∀ (a u : X) (M : Subgroup X), orderOf a = 2 → L ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))) → HeldTwoA L u →
      M ≤ centralizer ({u} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))) → conjugate M a ≠ M →
      gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u →
      (∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x) →
      ∀ c w : X, orderOf c = 2 → orderOf w = 2 → c * w = w * c →
        (c = u ∨ (u * w ≠ w * u ∧ ∃ k : ℕ, orderOf (u * w) = 2 * k ∧ c = (u * w) ^ k)) →
        M ≤ centralizer ({c} : Set X) →
        IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) →
        ∀ N : Subgroup X, N ≤ centralizer ({w} : Set X) →
          IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X))) →
          M ≤ (N ⊔ conjugate N c) ⊓ centralizer ({c} : Set X) →
          IsPComponent 2 (M.subgroupOf ((N ⊔ conjugate N c) ⊓ centralizer ({c} : Set X))) →
          conjugate N c ≠ N → gsFixedLayer (N ⊔ conjugate N c) c = M → False

end CFSG.ComponentClassification.GrSLit
