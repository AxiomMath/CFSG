module

public import CFSG.LargeExtraspecial.AS35CS63Star

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S63

structure SmithHyp {X : Type} [Group X] (ζ : X) (F : Subgroup X) : Prop where
  orderOf_eq : orderOf ζ = 2
  oddCore : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥
  le_centralizer : F ≤ centralizer ({ζ} : Set X)
  conj_mem : ∀ c ∈ centralizer ({ζ} : Set X), ∀ f ∈ F, c * f * c⁻¹ ∈ F
  extraspecial : IsExtraspecialPGroup 2 F
  zeta_mem : ζ ∈ F
  width : 2 ^ 5 ≤ Nat.card F
  elemAb : ∀ a ∈ F ⊔ centralizer (F : Set X), ∀ b ∈ F ⊔ centralizer (F : Set X),
    a * b * a⁻¹ * b⁻¹ ∈ zpowers ζ ∧ a * a ∈ zpowers ζ
  conj_mem_E : ∀ τ : X, IsConj ζ τ → τ * ζ = ζ * τ → τ ∈ F ⊔ centralizer (F : Set X)
  conj_mem_F : ∀ τ ∈ F, IsConj ζ τ → τ = ζ

structure SmithConf {X : Type} [Group X] (ζ : X) (F : Subgroup X) : Prop where
  hyp : SmithHyp ζ F
  setup : Timmesfeld.CorB.Setup ζ
  star : StarHyp ζ
  fusionF : ∀ τ ∈ Timmesfeld.CorB.conjCent ζ, τ ≠ ζ → ∃ f ∈ F, f * τ * f⁻¹ = ζ * τ
  nonIsolated : ∃ τ ∈ Timmesfeld.CorB.conjCent ζ, τ ≠ ζ

abbrev UZ {X : Type} [Group X] (ζ : X) : Type :=
  ↥(normalClosure ({ζ} : Set X)) ⧸ center ↥(normalClosure ({ζ} : Set X))

@[expose] def Smith55Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ζ : X) (F : Subgroup X), SmithConf ζ F →
    BenderSuzuki.IsBenderGroup (UZ ζ) → False

@[expose] def Smith58Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ζ : X) (F : Subgroup X), SmithConf ζ F →
    Blueprint.LieModel (UZ ζ) .trialityD4 0 2 1 → False

@[expose] def Smith59Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ζ : X) (F : Subgroup X), SmithConf ζ F →
    Blueprint.LieModel (UZ ζ) .PSU 3 3 1 → False

@[expose] def J2SchurInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], commutator Y = ⊤ →
    Blueprint.NativeSporadic.IsSporadic (Y ⧸ center Y) .J2 → Nat.card (center Y) ≤ 2

end S63

end CFSG.LargeExtraspecial
