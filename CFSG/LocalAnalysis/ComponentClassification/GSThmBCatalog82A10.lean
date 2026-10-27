module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CF82A10P : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    Nonempty (↥(generalizedFitting H) ≃* alternatingGroup (Fin 10)) →
    ∀ ι : H, orderOf ι = 2 →
    ∀ J₁ : Subgroup H, J₁ ≤ centralizer ({ι} : Set H) →
      IsPComponent 2 (J₁.subgroupOf (centralizer ({ι} : Set H))) →
      IsSec8JType (↥J₁ ⧸ pPrimeCore 2 ↥J₁) p f →
      Blueprint.LieModel (↥J₁ ⧸ pPrimeCore 2 ↥J₁) .PSL 2 3 2 ∧
      (∀ Q : Subgroup H, IsPGroup 2 Q → Q ≤ J₁ → Nat.card Q ≤ 8) ∧
      ∀ R : Subgroup H, IsPGroup 2 R → R ≤ centralizer ({ι} : Set H) ⊓ coreActionKernel J₁ →
        Nat.card R ≤ 8 ∧ (Nat.card R = 8 → ∃ u ∈ R, ∃ v ∈ R, u * v ≠ v * u)

@[expose] def CF82L2NineAbelian : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Blueprint.LieModel Y .PSL 2 3 2 →
    ∀ A : Subgroup (MulAut Y), IsPGroup 2 A → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      Nat.card A ≤ 8

end CFSG.ComponentClassification.GSThmB
