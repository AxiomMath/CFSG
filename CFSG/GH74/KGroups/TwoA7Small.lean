module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.KGroups.TwoA7

open Equiv Equiv.Perm Subgroup

theorem eq_one_of_comm_gens5 : ∀ g : Perm (Fin 5),
    g * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * g →
    g * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * g → g = 1 := by
  decide +kernel

theorem hC_alt5 : ∀ g : Perm (Fin 5), (∀ b ∈ alternatingGroup (Fin 5), g * b = b * g) →
    g ∈ alternatingGroup (Fin 5) := by
  intro g hg
  have h1 : g = 1 := eq_one_of_comm_gens5 g
    (hg _ (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)))
    (hg _ (Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)))
  rw [h1]
  exact Subgroup.one_mem _

theorem hBodd_alt5 : ∀ N : Subgroup (Perm (Fin 5)),
    (∀ b ∈ alternatingGroup (Fin 5), ∀ x ∈ N, b * x * b⁻¹ ∈ N) → ¬ 2 ∣ Nat.card N →
    N ⊓ alternatingGroup (Fin 5) = ⊥ := by
  intro N hN hodd
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by norm_num)
  set K : Subgroup (alternatingGroup (Fin 5)) := (N ⊓ alternatingGroup (Fin 5)).subgroupOf
    (alternatingGroup (Fin 5)) with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk a => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨?_, (a * k * a⁻¹).2⟩
    have := hN a a.2 k hk.1
    simpa using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h0 | h0
  · rw [hK, Subgroup.subgroupOf_eq_bot] at h0
    exact h0.eq_bot_of_le inf_le_right
  · exfalso
    apply hodd
    have hle : alternatingGroup (Fin 5) ≤ N := by
      intro a ha
      have : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ K := by rw [h0]; exact Subgroup.mem_top _
      rw [hK, Subgroup.mem_subgroupOf] at this
      exact this.1
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have := Subgroup.card_dvd_of_le hle
    rw [h60] at this
    exact (show 2 ∣ 60 by norm_num).trans this

@[expose] def V4list : List (Perm (Fin 4)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem V4_mul : ∀ x ∈ V4list, ∀ y ∈ V4list, x * y ∈ V4list := by decide +kernel

theorem V4_inv : ∀ x ∈ V4list, x⁻¹ ∈ V4list := by decide +kernel

@[expose] def V4 : Subgroup (Perm (Fin 4)) where
  carrier := {x | x ∈ V4list}
  one_mem' := by decide +kernel
  mul_mem' := fun {x y} hx hy => V4_mul x hx y hy
  inv_mem' := fun {x} hx => V4_inv x hx

theorem mem_V4 {x : Perm (Fin 4)} : x ∈ V4 ↔ x ∈ V4list := Iff.rfl

instance V4_normal : V4.Normal :=
  ⟨fun x hx g => by
    have : ∀ g : Perm (Fin 4), ∀ x ∈ V4list, g * x * g⁻¹ ∈ V4list := by decide +kernel
    exact this g x hx⟩

theorem V4_le_alternating : V4 ≤ alternatingGroup (Fin 4) := by
  intro x hx
  have : ∀ x ∈ V4list, Perm.sign x = 1 := by decide +kernel
  exact Equiv.Perm.mem_alternatingGroup.2 (this x hx)

theorem V4_sq : ∀ x ∈ V4list, x * x = 1 := by decide +kernel

theorem hC_V4 : ∀ g : Perm (Fin 4), (∀ b ∈ V4, g * b = b * g) → g ∈ V4 := by
  have key : ∀ g : Perm (Fin 4), g * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * g →
      g * (swap 0 2 * swap 1 3) = (swap 0 2 * swap 1 3) * g → g ∈ V4list := by decide +kernel
  intro g hg
  exact key g (hg _ (mem_V4.2 (by decide +kernel))) (hg _ (mem_V4.2 (by decide +kernel)))

theorem hBodd_V4 : ∀ N : Subgroup (Perm (Fin 4)),
    (∀ b ∈ V4, ∀ x ∈ N, b * x * b⁻¹ ∈ N) → ¬ 2 ∣ Nat.card N → N ⊓ V4 = ⊥ := by
  intro N _ hodd
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx2 : x * x = 1 := V4_sq x hx.2
  have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have hdvd : orderOf x ∣ Nat.card N := by
    exact Subgroup.orderOf_dvd_natCard N hx.1
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact h
    · exfalso
      exact hodd (h ▸ hdvd)
  exact orderOf_eq_one_iff.1 h1

end CFSG.GH74.KGroups.TwoA7
