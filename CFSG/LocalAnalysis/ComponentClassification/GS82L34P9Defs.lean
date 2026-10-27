module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalCentre
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def L34ExpFourPumpLeaf : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) →
    Blueprint.Catalog S → ∀ (σ : MulAut S) (P : Subgroup S), ProperFixedComponent σ P →
    GrSLit.IsL34Type (↥P ⧸ Open.fusionZStar ↥P) →
      (Blueprint.NativeSporadic.IsSporadic S .He ∧ ∀ z ∈ Open.fusionZStar ↥P, z * z = 1) ∨
      (Blueprint.NativeSporadic.IsSporadic S .ONan ∧ Nat.card ↥(Open.fusionZStar ↥P) = 4) ∨
      (Open.fusionZStar ↥P = ⊥ ∧ GrSLit.CentreTwoPartLe S 2)

@[expose] def L34ExpFourFixedLeaf : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → IsPGroup 2 ↥(center Q) →
    Blueprint.Catalog (Q ⧸ center Q) → ∀ σ : MulAut Q, (∀ y, σ (σ y) = y) →
    ∀ P : Subgroup Q, P ≤ fixedSubgroup σ → IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) →
      P ≠ ⊤ → GH74.GLS.IsL34Quotient (↥P ⧸ pPrimeCore 2 ↥P) →
      ¬ IsElementaryAbelian 2 ↥(center (↥P ⧸ pPrimeCore 2 ↥P)) →
      Blueprint.NativeSporadic.IsSporadic (Q ⧸ center Q) .ONan ∧
        IsCyclic ↥(center (↥P ⧸ pPrimeCore 2 ↥P)) ∧
        Nat.card ↥(center (↥P ⧸ pPrimeCore 2 ↥P)) = 4

end CFSG.ComponentClassification.GS82PumpInputs
