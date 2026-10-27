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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

abbrev V6 : Type := Fin 6 → ZMod 2

@[expose] def qm (x : V6) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5

@[expose] def lam (x : V6) : ZMod 2 := x 5

@[expose] def qp (x : V6) : ZMod 2 := qm x + lam x

@[expose] def tv : V6 := Pi.single 4 1

@[expose] def bil (x y : V6) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 + x 4 * y 5 + x 5 * y 4

set_option maxRecDepth 100000 in
theorem qm_add (x y : V6) : qm (x + y) = qm x + qm y + bil x y := by
  revert x y
  decide +kernel

theorem qp_add (x y : V6) : qp (x + y) = qp x + qp y + bil x y := by
  have h := qm_add x y
  have hl : lam (x + y) = lam x + lam y := rfl
  simp only [qp, hl, h]
  ring

theorem lam_eq_bil (x : V6) : lam x = bil x tv := by
  simp [lam, bil, tv, Pi.single_apply]

theorem bil_comm (x y : V6) : bil x y = bil y x := by
  simp only [bil]
  ring

theorem bil_self (x : V6) : bil x x = 0 := by
  simp only [bil]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp [h2]

theorem bil_add_left (x y z : V6) : bil (x + y) z = bil x z + bil y z := by
  simp only [bil, Pi.add_apply]
  ring

theorem bil_add_right (x y z : V6) : bil x (y + z) = bil x y + bil x z := by
  simp only [bil, Pi.add_apply]
  ring

theorem bil_smul_left (c : ZMod 2) (x y : V6) : bil (c • x) y = c * bil x y := by
  simp only [bil, Pi.smul_apply, smul_eq_mul]
  ring

set_option maxRecDepth 100000 in
theorem transv_involutive (x u : V6) : (x + bil x u • u) + bil (x + bil x u • u) u • u = x := by
  revert x u
  decide +kernel

@[expose] def transv (u : V6) : Equiv.Perm V6 where
  toFun x := x + bil x u • u
  invFun x := x + bil x u • u
  left_inv x := transv_involutive x u
  right_inv x := transv_involutive x u

@[expose] def IsAddPerm (g : Equiv.Perm V6) : Prop := ∀ x y, g (x + y) = g x + g y

@[expose] def OrthOf (q : V6 → ZMod 2) : Subgroup (Equiv.Perm V6) where
  carrier := {g | IsAddPerm g ∧ ∀ x, q (g x) = q x}
  mul_mem' := by
    rintro g h ⟨hg, hgq⟩ ⟨hh, hhq⟩
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [hh, hg]
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [hgq, hhq]
  one_mem' := ⟨fun x y => rfl, fun x => rfl⟩
  inv_mem' := by
    rintro g ⟨hg, hgq⟩
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · apply g.injective
      rw [hg]
      simp
    · have := hgq (g⁻¹ x)
      simpa using this.symm

@[expose] def OrthMinus : Subgroup (Equiv.Perm V6) := OrthOf qm

@[expose] def OrthPlus : Subgroup (Equiv.Perm V6) := OrthOf qp

@[expose] def OmegaOf (q : V6 → ZMod 2) : Subgroup (Equiv.Perm V6) :=
  Subgroup.closure {g | ∃ u v : V6, q u = 1 ∧ q v = 1 ∧ g = transv u * transv v}

@[expose] def OmegaMinus : Subgroup (Equiv.Perm V6) := OmegaOf qm

@[expose] def OmegaPlus : Subgroup (Equiv.Perm V6) := OmegaOf qp

@[expose] def Yv2 : Finset V6 :=
  Finset.univ.filter fun x => x = tv ∨ (lam x = 1 ∧ qm x = 0)

@[expose] def Yv1 : Finset V6 :=
  Finset.univ.filter fun x => x = tv ∨ (lam x = 1 ∧ qm x = 1)

@[expose] def Yv12 : Finset V6 :=
  Finset.univ.filter fun x => x = tv ∨ lam x = 1

@[expose] def X48 : Finset V6 :=
  Finset.univ.filter fun x => (lam x = 0 ∧ qm x = 1) ∨ lam x = 1

@[expose] def X36 : Finset V6 := Finset.univ.filter fun x => qm x = 1

@[expose] def X28 : Finset V6 := Finset.univ.filter fun x => qp x = 1

set_option maxRecDepth 100000 in
theorem card_X36 : X36.card = 36 := by decide +kernel

set_option maxRecDepth 100000 in
theorem card_X28 : X28.card = 28 := by decide +kernel

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
