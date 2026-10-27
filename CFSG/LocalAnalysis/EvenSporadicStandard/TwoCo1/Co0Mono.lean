module

public import CFSG.Monster.VisQuot.Monomial
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot

theorem gO_injective : Function.Injective gO := fun a b h =>
  (gO_mul_PO_inj (a := a) (b := b) (p := 1) (q := 1) (by rw [PO_one, mul_one, mul_one]; exact h)).1

theorem gO_inv (a : C) : (gO a)⁻¹ = gO a := inv_eq_of_mul_eq_one_right (gO_mul_self a)

theorem gO_add' (a b : C) : gO a * gO b = gO (a + b) := (gO_add a b).symm

theorem PO_mul_gO' (p : AutPerm) (a : C) :
    PO p * gO a * (PO p)⁻¹ = gO ((permC p).symm a) := by
  rw [PO_mul_gO, mul_inv_cancel_right]

@[expose] def monoSub (H : Subgroup AutPerm) : Subgroup latticeO where
  carrier := {g | ∃ a : C, ∃ p ∈ H, g = gO a * PO p}
  one_mem' := ⟨0, 1, H.one_mem, by rw [gO_zero, PO_one, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨a, p, hp, rfl⟩ ⟨b, q, hq, rfl⟩
    refine ⟨a + (permC p).symm b, q * p, H.mul_mem hq hp, ?_⟩
    rw [gO_add, PO_mul, mul_assoc, ← mul_assoc (PO p), PO_mul_gO]
    simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, p, hp, rfl⟩
    refine ⟨(permC p⁻¹).symm a, p⁻¹, H.inv_mem hp, ?_⟩
    rw [_root_.mul_inv_rev, gO_inv, ← PO_inv, PO_mul_gO]

theorem gO_mem_monoSub (H : Subgroup AutPerm) (a : C) : gO a ∈ monoSub H :=
  ⟨a, 1, H.one_mem, by rw [PO_one, mul_one]⟩

theorem PO_mem_monoSub {H : Subgroup AutPerm} {p : AutPerm} (hp : p ∈ H) : PO p ∈ monoSub H :=
  ⟨0, p, hp, by rw [gO_zero, one_mul]⟩

theorem monoSub_mono {H H' : Subgroup AutPerm} (h : H ≤ H') : monoSub H ≤ monoSub H' :=
  fun _ ⟨a, p, hp, e⟩ => ⟨a, p, h hp, e⟩

theorem natCard_C : Nat.card C = 2 ^ 12 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_C]

theorem card_monoSub (H : Subgroup AutPerm) : Nat.card (monoSub H) = 2 ^ 12 * Nat.card H := by
  rw [← natCard_C, ← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : C × H => (⟨gO x.1 * PO x.2, x.1, x.2, x.2.2, rfl⟩ : monoSub H)) ⟨?_, ?_⟩)).symm
  · intro x y hxy
    have h := gO_mul_PO_inj (congrArg Subtype.val hxy)
    exact Prod.ext h.1 (Subtype.ext h.2)
  · rintro ⟨_, a, p, hp, rfl⟩
    exact ⟨(a, ⟨p, hp⟩), rfl⟩

theorem mul_PO_mem_centralizer_gO_iff (a : C) (p : AutPerm) (d : C) :
    gO a * PO p ∈ Subgroup.centralizer {gO d} ↔ permC p d = d := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : gO a * PO p * gO d = gO a * gO ((permC p).symm d) * PO p := by
    rw [mul_assoc, PO_mul_gO, ← mul_assoc]
  have h2 : gO d * (gO a * PO p) = gO a * gO d * PO p := by
    rw [← mul_assoc, gO_comm d a]
  rw [h1, h2, mul_left_inj, mul_right_inj, gO_injective.eq_iff, LinearEquiv.symm_apply_eq, eq_comm]

end CFSG.EvenSporadicStandard.TwoCo1
