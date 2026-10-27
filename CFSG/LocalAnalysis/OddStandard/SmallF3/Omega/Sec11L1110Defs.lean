module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {E : Type} [Group E]

@[expose] def ActsTrivModZ (z s : E) (Q : Subgroup E) : Prop :=
  ∀ a ∈ Q, s * a * s⁻¹ * a⁻¹ ∈ zpowers z

structure Sec11Q8Pair (z : E) (Q1 Q2 : Subgroup E) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_mem1 : z ∈ Q1
  z_mem2 : z ∈ Q2
  comm : ∀ a ∈ Q1, ∀ b ∈ Q2, a * b = b * a
  inf : ∀ x ∈ Q1, x ∈ Q2 → x ∈ zpowers z
  elem1 : ∀ a ∈ Q1, ∀ b ∈ Q1, a * b * a⁻¹ * b⁻¹ ∈ zpowers z ∧ a * a ∈ zpowers z
  elem2 : ∀ a ∈ Q2, ∀ b ∈ Q2, a * b * a⁻¹ * b⁻¹ ∈ zpowers z ∧ a * a ∈ zpowers z
  center1 : ∀ a ∈ Q1, (∀ b ∈ Q1, a * b = b * a) → a ∈ zpowers z
  center2 : ∀ a ∈ Q2, (∀ b ∈ Q2, a * b = b * a) → a ∈ zpowers z
  invol1 : ∀ a ∈ Q1, a * a = 1 → a ∈ zpowers z
  invol2 : ∀ a ∈ Q2, a * a = 1 → a ∈ zpowers z
  card1 : Nat.card ↥Q1 = 8
  card2 : Nat.card ↥Q2 = 8

end CFSG.OddStandard.SmallF3.Omega
