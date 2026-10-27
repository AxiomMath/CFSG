module

public import CFSG.Blueprint.Catalog

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup

@[expose] def CorBList (Y : Type) [Group Y] : Prop :=
  (∃ f, Blueprint.LieModel Y .PSL 2 2 f) ∨ (∃ f, Blueprint.LieModel Y .PSU 3 2 f) ∨
    (∃ f, Blueprint.LieModel Y .twistedB2 0 2 f) ∨ (∃ f, Blueprint.LieModel Y .PSL 3 2 f) ∨
    (∃ f, Blueprint.LieModel Y .G2 0 2 f) ∨ Blueprint.LieModel Y .PSU 3 3 1 ∨
    (∃ f, Blueprint.LieModel Y .trialityD4 0 2 f) ∨
    Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨ Blueprint.NativeSporadic.IsSporadic Y .J2

@[expose] def conjCent {X : Type*} [Group X] (t : X) : Set X := {τ | τ * t = t * τ ∧ IsConj t τ}

@[expose] def TimmesfeldCorBInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : X), orderOf t = 2 →
    IsPGroup 2 (closure (conjCent t)) →
    ⁅⁅closure (conjCent t), closure (conjCent t)⁆, closure (conjCent t)⁆ = ⊥ →
    (∀ τ : X, τ * t = t * τ → IsConj t τ → τ ≠ t → IsConj t (t * τ)) →
    (∃ K : Subgroup X, K ≤ normalClosure {t} ∧ (K.subgroupOf (normalClosure {t})).Normal ∧
        Odd (Nat.card K) ∧ normalClosure {t} = K ⊔ zpowers t) ∨
      (∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
        x * y = y * x ∧ x * x = 1) ∨
      CorBList (↥(normalClosure ({t} : Set X)) ⧸ center ↥(normalClosure ({t} : Set X)))

@[expose] def CorBListFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (U : Subgroup X), U.Normal →
    CorBList (↥U ⧸ center ↥U) →
    IsSimpleGroup (↥U ⧸ center ↥U) ∧
    (⁅U, U⁆ = U → ∃ k, derivedSeries X k ≤ U ⊔ centralizer (U : Set X)) ∧
    ∀ t ∈ U, orderOf t = 2 → (∃ u ∈ U, u * t ≠ t * u) →
      ∀ R N : Subgroup X, N ≤ R → R ≤ U ⊓ centralizer ({t} : Set X) →
        ∀ (_ : (N.subgroupOf R).Normal), IsSimpleGroup (↥R ⧸ N.subgroupOf R) →
          ∃ P : Sylow 2 (↥R ⧸ N.subgroupOf R),
            ∀ x ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)),
              ∀ y ∈ (P : Subgroup (↥R ⧸ N.subgroupOf R)), x * y = y * x

end CFSG.LargeExtraspecial.S8
