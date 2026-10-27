module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NOne

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

@[expose] def innerImage (Y : Type*) [Group Y] (F : Subgroup Y) : Subgroup (MulAut Y) :=
  F.map (MulAut.conj : Y →* MulAut Y)

@[expose] def autOrbit {Y : Type*} [Group Y] (S : Subgroup (MulAut Y)) (y : Y) : Set Y :=
  {y' | ∃ α ∈ S, y' = α y}

@[expose] def autConjClass {Y : Type*} [Group Y] (S : Subgroup (MulAut Y)) (β : MulAut Y) :
    Set (MulAut Y) :=
  {β' | ∃ α ∈ S, β' = α * β * α⁻¹}

structure E16Facts (Y : Type*) [Group Y] (S : Subgroup (MulAut Y)) (F : Subgroup Y) : Prop where
  card : Nat.card F = 16
  sq : ∀ x ∈ F, x * x = 1
  comm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  normal : ∀ α ∈ S, ∀ x, x ∈ F ↔ α x ∈ F
  inner_le : innerImage Y F ≤ S
  cent : ∀ α : MulAut Y, (∀ x ∈ F, α x = x) → α ∈ innerImage Y F
  orbit8 : ∃ x ∈ F, x ≠ 1 ∧ (autOrbit S x).ncard = 8
  unique : ∀ E : Subgroup (MulAut Y), E ≤ S → (∀ α ∈ S, ∀ β ∈ E, α * β * α⁻¹ ∈ E) →
    (∀ α ∈ E, ∀ β ∈ E, α * β = β * α) → (∀ α ∈ E, α * α = 1) → Nat.card E = 16 →
    (∀ γ ∈ S, (∀ β ∈ E, γ * β = β * γ) → γ ∈ E) →
    (∃ β ∈ E, β ≠ 1 ∧ (autConjClass S β).ncard = 8) → E = innerImage Y F

structure SylowWitness (Y : Type) [Group Y] (S : Subgroup (MulAut Y)) (t : Y) (F : Subgroup Y) :
    Prop where
  sq : t * t = 1
  ne : t ≠ 1
  fourth : ∃ g : Y, g * g * (g * g) = t
  mem : MulAut.conj t ∈ S
  center : ∀ α ∈ S, (∀ β ∈ S, β * α = α * β) ↔ (α = 1 ∨ α = MulAut.conj t)
  t_mem : t ∈ F
  nd : NData (⊤ : Subgroup Y) F
  e16 : E16Facts Y S F
  card_S : Nat.card S = 256
  outer_inv : ∃ s ∈ S, s ∉ innerImage Y ⊤ ∧ s * s = 1
  count_ne : {s : MulAut Y | s ∈ S ∧ s ∉ innerImage Y ⊤ ∧ s * s = 1}.ncard ≠
    {s : MulAut Y | s ∈ S ∧ s ∉ innerImage Y ⊤ ∧ s * s = MulAut.conj t}.ncard

@[expose] def AutSylowFacts (Y : Type) [Group Y] : Prop :=
  ∀ S : Subgroup (MulAut Y), IsPGroup 2 S → ¬ 2 ∣ S.index → ∃ (t : Y) (F : Subgroup Y),
    SylowWitness Y S t F

end CFSG.EvenSporadicStandard.M22Std
