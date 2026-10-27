module

public import CFSG.LargeExtraspecial.S8CorBStatement
public import CFSG.Foundations.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup

@[expose] def CorBListA5Facts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X), orderOf t = 2 →
    IsPGroup 2 (closure (conjCent t)) →
    ⁅⁅closure (conjCent t), closure (conjCent t)⁆, closure (conjCent t)⁆ = ⊥ →
    (∀ τ : X, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ)) →
    CorBList (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X))) →
    ∀ R N : Subgroup X, N ≤ R → R ≤ normalClosure ({t} : Set X) →
      R ≤ centralizer ({t} : Set X) →
      (∀ c : X, c * t = t * c → ∀ r ∈ R, c * r * c⁻¹ ∈ R) →
      ⁅R, R⁆ = R → ∀ (_ : (N.subgroupOf R).Normal), t ∈ N →
      IsSimpleGroup (↥R ⧸ N.subgroupOf R) → Nat.card (↥R ⧸ N.subgroupOf R) = 60 →
      IsExtraspecialPGroup 2 N → Nat.card N < 2 ^ 9

end CFSG.LargeExtraspecial.S8
