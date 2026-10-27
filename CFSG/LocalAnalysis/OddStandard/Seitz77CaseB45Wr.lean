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
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.OddStandard.Seitz77

@[ext] structure Wr (Q : Type*) where
  a : Q
  b : Q
  e : Bool

namespace Wr

section Group

variable {Q : Type*} [Group Q]

instance : Mul (Wr Q) :=
  ⟨fun x y => ⟨x.a * (cond x.e y.b y.a), x.b * (cond x.e y.a y.b), xor x.e y.e⟩⟩

instance : One (Wr Q) := ⟨⟨1, 1, false⟩⟩

instance : Inv (Wr Q) :=
  ⟨fun x => ⟨cond x.e x.b⁻¹ x.a⁻¹, cond x.e x.a⁻¹ x.b⁻¹, x.e⟩⟩

theorem mul_def (x y : Wr Q) :
    x * y = ⟨x.a * (cond x.e y.b y.a), x.b * (cond x.e y.a y.b), xor x.e y.e⟩ := rfl

theorem one_def : (1 : Wr Q) = ⟨1, 1, false⟩ := rfl

theorem inv_def (x : Wr Q) : x⁻¹ = ⟨cond x.e x.b⁻¹ x.a⁻¹, cond x.e x.a⁻¹ x.b⁻¹, x.e⟩ := rfl

@[simp] theorem mk_mul_mk_false (a b c d : Q) (f : Bool) :
    (⟨a, b, false⟩ : Wr Q) * ⟨c, d, f⟩ = ⟨a * c, b * d, f⟩ := by
  cases f <;> rfl

@[simp] theorem mk_mul_mk_true (a b c d : Q) (f : Bool) :
    (⟨a, b, true⟩ : Wr Q) * ⟨c, d, f⟩ = ⟨a * d, b * c, !f⟩ := by
  cases f <;> rfl

@[simp] theorem mk_inv_false (a b : Q) : (⟨a, b, false⟩ : Wr Q)⁻¹ = ⟨a⁻¹, b⁻¹, false⟩ := rfl

@[simp] theorem mk_inv_true (a b : Q) : (⟨a, b, true⟩ : Wr Q)⁻¹ = ⟨b⁻¹, a⁻¹, true⟩ := rfl

instance : Group (Wr Q) where
  mul_assoc x y z := by
    obtain ⟨a, b, e⟩ := x
    obtain ⟨c, d, f⟩ := y
    obtain ⟨g, h, k⟩ := z
    cases e <;> cases f <;> cases k <;> simp [mul_assoc]
  one_mul x := by
    obtain ⟨a, b, e⟩ := x
    cases e <;> simp [one_def]
  mul_one x := by
    obtain ⟨a, b, e⟩ := x
    cases e <;> simp [one_def]
  inv_mul_cancel x := by
    obtain ⟨a, b, e⟩ := x
    cases e <;> simp [one_def]

@[simp] theorem one_a : (1 : Wr Q).a = 1 := rfl

@[simp] theorem one_b : (1 : Wr Q).b = 1 := rfl

@[simp] theorem one_e : (1 : Wr Q).e = false := rfl

@[expose] def swap : Wr Q := ⟨1, 1, true⟩

@[simp] theorem swap_e : (swap : Wr Q).e = true := rfl

theorem swap_mul_swap : (swap : Wr Q) * swap = 1 := by
  simp [swap, one_def]

theorem swap_inv : (swap : Wr Q)⁻¹ = swap := by
  simp [swap]

theorem swap_mul_mul_swap (a b : Q) : (swap : Wr Q) * ⟨a, b, false⟩ * swap = ⟨b, a, false⟩ := by
  simp [swap]

theorem sq_true (a b : Q) : (⟨a, b, true⟩ : Wr Q) * ⟨a, b, true⟩ = ⟨a * b, b * a, false⟩ := by
  simp

theorem eq_of_mul_self_eq_one_of_e {a b : Q} (h : (⟨a, b, true⟩ : Wr Q) * ⟨a, b, true⟩ = 1) :
    b = a⁻¹ := by
  rw [sq_true, one_def] at h
  have h1 : a * b = 1 := congrArg Wr.a h
  exact eq_inv_of_mul_eq_one_right h1

end Group

section Hom

variable {Q Q' : Type*} [Group Q] [Group Q']

@[expose] def map (f : Q →* Q') : Wr Q →* Wr Q' where
  toFun x := ⟨f x.a, f x.b, x.e⟩
  map_one' := by simp [one_def]
  map_mul' x y := by
    obtain ⟨a, b, e⟩ := x
    obtain ⟨c, d, g⟩ := y
    cases e <;> simp

@[simp] theorem map_apply (f : Q →* Q') (x : Wr Q) : map f x = ⟨f x.a, f x.b, x.e⟩ := rfl

theorem map_injective {f : Q →* Q'} (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro x y h
  have h1 : f x.a = f y.a := congrArg (fun w : Wr Q' => w.a) h
  have h2 : f x.b = f y.b := congrArg (fun w : Wr Q' => w.b) h
  have h3 : x.e = y.e := congrArg (fun w : Wr Q' => w.e) h
  exact Wr.ext (hf h1) (hf h2) h3

@[expose] def eHom : Wr Q →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (if x.e then 1 else 0)
  map_one' := by simp [one_def]
  map_mul' x y := by
    obtain ⟨a, b, e⟩ := x
    obtain ⟨c, d, g⟩ := y
    cases e <;> cases g <;> simp [mul_def]
    decide

theorem eHom_eq_one_iff (x : Wr Q) : eHom x = 1 ↔ x.e = false := by
  obtain ⟨a, b, e⟩ := x
  cases e <;> simp [eHom]

end Hom

section Sub

variable {Q : Type*} [Group Q]

@[expose] def sub (H : Subgroup Q) : Subgroup (Wr Q) where
  carrier := {x | x.a ∈ H ∧ x.b ∈ H}
  one_mem' := ⟨H.one_mem, H.one_mem⟩
  mul_mem' := by
    rintro ⟨a, b, e⟩ ⟨c, d, g⟩ ⟨ha, hb⟩ ⟨hc, hd⟩
    cases e <;> simp_all [H.mul_mem]
  inv_mem' := by
    rintro ⟨a, b, e⟩ ⟨ha, hb⟩
    cases e <;> simp_all [H.inv_mem]

theorem mem_sub {H : Subgroup Q} {x : Wr Q} : x ∈ sub H ↔ x.a ∈ H ∧ x.b ∈ H := Iff.rfl

@[expose] def base : Subgroup (Wr Q) :=
  eHom.ker

theorem mem_base {x : Wr Q} : x ∈ (base : Subgroup (Wr Q)) ↔ x.e = false := by
  rw [base, MonoidHom.mem_ker, eHom_eq_one_iff]

@[expose] def ss (U : Subgroup Q) : Subgroup (Wr Q) := sub U ⊓ base

theorem mem_ss {U : Subgroup Q} {x : Wr Q} : x ∈ ss U ↔ x.a ∈ U ∧ x.b ∈ U ∧ x.e = false := by
  rw [ss, Subgroup.mem_inf, mem_base]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

@[expose] def equivProd (Q : Type*) : Wr Q ≃ Q × Q × Bool where
  toFun x := (x.a, x.b, x.e)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite Q] : Finite (Wr Q) :=
  Finite.of_equiv _ (equivProd Q).symm

omit [Group Q] in
theorem natCard [Finite Q] : Nat.card (Wr Q) = Nat.card Q ^ 2 * 2 := by
  rw [Nat.card_congr (equivProd Q), Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool)]
  simp [sq, mul_assoc]

theorem natCard_sub [Finite Q] (H : Subgroup Q) : Nat.card (sub H) = Nat.card H ^ 2 * 2 := by
  have e : sub H ≃ H × H × Bool :=
    { toFun := fun x => (⟨x.1.a, x.2.1⟩, ⟨x.1.b, x.2.2⟩, x.1.e)
      invFun := fun p => ⟨⟨p.1.1, p.2.1.1, p.2.2⟩, p.1.2, p.2.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool)]
  simp [sq, mul_assoc]

theorem natCard_ss (U : Subgroup Q) : Nat.card (ss U) = Nat.card U ^ 2 := by
  have e : ss U ≃ U × U :=
    { toFun := fun x => (⟨x.1.a, (mem_ss.1 x.2).1⟩, ⟨x.1.b, (mem_ss.1 x.2).2.1⟩)
      invFun := fun p => ⟨⟨p.1.1, p.2.1, false⟩, mem_ss.2 ⟨p.1.2, p.2.2, rfl⟩⟩
      left_inv := fun x => by
        obtain ⟨⟨a, b, e⟩, hx⟩ := x
        have := (mem_ss.1 hx).2.2
        simp only at this
        subst this
        rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, sq]

end Sub

end Wr

end CFSG.OddStandard.Seitz77
