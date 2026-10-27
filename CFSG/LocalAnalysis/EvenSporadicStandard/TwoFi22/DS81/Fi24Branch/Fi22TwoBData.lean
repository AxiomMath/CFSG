module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBGens

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup
open Fi22TwoB (Cbar t1)

structure Fi22TwoBData (Q : Subgroup (Equiv.Perm (Fin 3510))) : Prop where
  card_C : Nat.card Cbar = 2 ^ 18 * 3 ^ 4 * 5
  Q_le : Q ≤ Cbar
  card_Q : Nat.card Q = 2 ^ 11
  t1_mem : t1 ∈ Q
  sq : ∀ x ∈ Q, x ^ 2 ∈ zpowers t1
  comm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ zpowers t1
  center : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) ↔ x ∈ zpowers t1
  abelian : ∀ B : Subgroup (Equiv.Perm (Fin 3510)), B ≤ Q →
    (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Nat.card B ≤ 2 ^ 6
  cent : Cbar ⊓ centralizer (Q : Set (Equiv.Perm (Fin 3510))) ≤ Q
  O2 : TwoFi22.O2In Cbar = Q
  quot : ∃ (X : Type) (_ : Group X) (ρ : ↥Cbar →* X), Function.Surjective ρ ∧
    ρ.ker = Q.subgroupOf Cbar ∧ IsU42Two X
  perfect : ∃ Y : Subgroup (Equiv.Perm (Fin 3510)), Y ≤ Cbar ∧ ⁅Y, Y⁆ = Y ∧
    (Y ⊔ Q).relIndex Cbar = 2 ∧
    ∀ U : Subgroup (Equiv.Perm (Fin 3510)), zpowers t1 ≤ U → U ≤ Q → InvUnder Y U →
      Nat.card U = 2 ∨ Nat.card U = 2 ^ 2 ∨ Nat.card U = 2 ^ 10 ∨ Nat.card U = 2 ^ 11

@[expose] def Fi22TwoBFacts : Prop := ∃ Q, Fi22TwoBData Q

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
