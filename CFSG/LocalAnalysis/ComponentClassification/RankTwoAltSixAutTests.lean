module

public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm

@[expose] def sixC012 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def sixC013 : Perm (Fin 6) := swap 0 1 * swap 1 3

@[expose] def InV0 (x : Perm (Fin 6)) : Prop :=
  x = swap 0 1 * swap 2 3 ∨ x = swap 0 2 * swap 1 3 ∨ x = swap 0 3 * swap 1 2

instance (x : Perm (Fin 6)) : Decidable (InV0 x) := by unfold InV0; infer_instance

@[expose] def InVexo (x : Perm (Fin 6)) : Prop :=
  x = swap 0 1 * swap 2 3 ∨ x = swap 0 1 * swap 4 5 ∨ x = swap 2 3 * swap 4 5

instance (x : Perm (Fin 6)) : Decidable (InVexo x) := by unfold InVexo; infer_instance

@[expose] def fourConj6 : List (Perm (Fin 6)) :=
  [1, swap 3 4, swap 3 5 * swap 3 4, swap 1 3 * swap 1 4 * swap 1 2,
    swap 1 3 * swap 1 5 * swap 1 4 * swap 1 2, swap 1 4 * swap 1 2 * swap 3 5,
    swap 1 2 * swap 1 3 * swap 1 4, swap 1 2 * swap 1 3 * swap 1 5 * swap 1 4,
    swap 1 2 * swap 1 4 * swap 3 5, swap 1 3 * swap 1 5 * swap 1 2 * swap 1 4,
    swap 0 1 * swap 0 2 * swap 0 3 * swap 0 4, swap 0 1 * swap 0 2 * swap 0 3 * swap 0 5 * swap 0 4,
    swap 1 4 * swap 1 2, swap 1 5 * swap 1 4 * swap 1 2, swap 1 5 * swap 1 3 * swap 1 4 * swap 1 2,
    swap 0 1 * swap 0 2 * swap 0 4 * swap 3 5, swap 0 1 * swap 0 3 * swap 0 5 * swap 0 2 * swap 0 4,
    swap 0 2 * swap 0 4 * swap 1 3 * swap 1 5]

@[expose] def FourGood (a b : Perm (Fin 6)) : Prop :=
  ∃ σ ∈ fourConj6, (InV0 (σ * a * σ⁻¹) ∧ InV0 (σ * b * σ⁻¹)) ∨
    (InVexo (σ * a * σ⁻¹) ∧ InVexo (σ * b * σ⁻¹))

instance (a b : Perm (Fin 6)) : Decidable (FourGood a b) := by unfold FourGood; infer_instance

@[expose] def PairGood (a b : Perm (Fin 6)) : Prop :=
  b * b = 1 → b ≠ 1 → b ≠ a → a * b = b * a → sign b = 1 → FourGood a b

instance (a b : Perm (Fin 6)) : Decidable (PairGood a b) := by unfold PairGood; infer_instance

@[expose] def InvGood (a : Perm (Fin 6)) : Prop :=
  a * a = 1 → a ≠ 1 → sign a = 1 → ∀ b : Perm (Fin 6), PairGood a b

instance (a : Perm (Fin 6)) : Decidable (InvGood a) := by unfold InvGood; infer_instance

@[expose] def v0List : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

@[expose] def vexoList : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5]

@[expose] def ActsAsC (y : Perm (Fin 6)) : Prop :=
  sign y = 1 → (∀ u ∈ v0List, y * u * y⁻¹ = sixC012 * u * sixC012⁻¹) →
    ∃ v ∈ (1 : Perm (Fin 6)) :: v0List, y = v * sixC012 * v⁻¹

instance (y : Perm (Fin 6)) : Decidable (ActsAsC y) := by unfold ActsAsC; infer_instance

@[expose] def NormThree (y : Perm (Fin 6)) : Prop :=
  (∀ u ∈ v0List, y * u * y⁻¹ ∈ v0List) → y * y * y = 1 → y ≠ 1 → sign y = 1 →
    y.support.card = 3

instance (y : Perm (Fin 6)) : Decidable (NormThree y) := by unfold NormThree; infer_instance

@[expose] def SqFour (y : Perm (Fin 6)) : Prop :=
  y * swap 4 5 = swap 4 5 * y → sign y = 1 → y * y ≠ 1 → y * y * (y * y) = 1 → InV0 (y * y)

instance (y : Perm (Fin 6)) : Decidable (SqFour y) := by unfold SqFour; infer_instance

@[expose] def v0RootList : List (Perm (Fin 6)) :=
  [swap 0 2 * swap 2 1 * swap 1 3 * swap 4 5, swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5,
    swap 0 1 * swap 1 3 * swap 3 2 * swap 4 5]

@[expose] def CentSix (b : Perm (Fin 6)) : Prop :=
  b * sixC012 = sixC012 * b → b * sixC013 = sixC013 * b →
    b * (swap 0 1 * swap 4 5) = swap 0 1 * swap 4 5 * b → sign b = 1 → b = 1

instance (b : Perm (Fin 6)) : Decidable (CentSix b) := by unfold CentSix; infer_instance

@[expose] def sixAutCheck : Bool :=
  decide (∀ a : Perm (Fin 6), InvGood a) &&
  decide (∀ u ∈ v0List, ∀ v ∈ v0List, u ≠ v → u * v ∈ v0List) &&
  decide (∀ x₁ ∈ v0List, ∀ x₂ ∈ v0List, x₁ ≠ x₂ → ∀ e ∈ v0List, e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂) &&
  decide (∀ x₁ ∈ vexoList, ∀ x₂ ∈ vexoList, x₁ ≠ x₂ → ∀ e ∈ vexoList,
    e = x₁ ∨ e = x₂ ∨ e = x₁ * x₂) &&
  decide (∀ x ∈ v0List, ∀ y ∈ v0List, x * y = y * x) &&
  decide (∀ u ∈ v0List, u * u = 1) &&
  decide (∀ u ∈ v0List, u ≠ 1) &&
  decide (∀ u ∈ v0List, sign u = 1) &&
  decide (∀ u ∈ vexoList, sign u = 1) &&
  decide (∀ u ∈ v0List, sixC012 * u * sixC012⁻¹ ∈ v0List) &&
  decide (∀ y : Perm (Fin 6), ActsAsC y) &&
  decide (∀ y : Perm (Fin 6), NormThree y) &&
  decide (∀ y : Perm (Fin 6), SqFour y) &&
  decide (∀ u ∈ v0List, ∃ w ∈ v0RootList, w * w = u ∧ w * swap 4 5 = swap 4 5 * w ∧ sign w = 1) &&
  decide (∀ b : Perm (Fin 6), CentSix b)

end CFSG.ComponentClassification.RankTwoAlt
