module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup

variable {X : Type*} [Group X]

@[expose] def negAt (i : Fin 3) (c : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  Function.update c i (-c i)

@[expose] def eb (σ : Multiplicative (Fin 3 → ZMod 3) →* X) (i : Fin 3) : X :=
  σ (Multiplicative.ofAdd (Pi.single i 1))

structure EigenHyp (Y L : Subgroup X) : Prop where
  card_Y : Nat.card Y = 27
  card_L : Nat.card L = 8
  sq : ∀ x ∈ L, x * x = 1
  conj : ∀ x ∈ L, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y
  centY : ∀ y ∈ Y, (∀ x ∈ L, x * y = y * x) → y = 1
  centL : ∀ x ∈ L, (∀ y ∈ Y, x * y = y * x) → x = 1

structure EigenBasis (Y L : Subgroup X) (σ : Multiplicative (Fin 3 → ZMod 3) →* X)
    (l : Fin 3 → X) : Prop where
  inj : Function.Injective σ
  range_eq : σ.range = Y
  l_mem : ∀ i, l i ∈ L
  act : ∀ (i : Fin 3) (c : Fin 3 → ZMod 3),
    l i * σ (Multiplicative.ofAdd c) * (l i)⁻¹ = σ (Multiplicative.ofAdd (negAt i c))
  gen : L ≤ closure (Set.range l)

theorem negAt_negAt (i : Fin 3) (c : Fin 3 → ZMod 3) : negAt i (negAt i c) = c := by
  funext j
  by_cases h : j = i
  · subst h
    simp [negAt]
  · simp [negAt, h]

end CFSG.GF2Type.Smith1979.TriPlus

end
