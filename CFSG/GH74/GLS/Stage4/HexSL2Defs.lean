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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Hex

abbrev SL2 (F : Type*) [Field F] : Type _ := Matrix.SpecialLinearGroup (Fin 2) F

section Elements

variable {F : Type*} [Field F]

@[expose] def sl2U (c : F) : SL2 F := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2L (c : F) : SL2 F := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2D (t : Fˣ) : SL2 F :=
  ⟨!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

variable (F) in
@[expose] def sl2W : SL2 F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_sl2U (c : F) : (sl2U c : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := rfl

@[simp] theorem coe_sl2L (c : F) : (sl2L c : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

@[simp] theorem coe_sl2D (t : Fˣ) :
    (sl2D t : Matrix (Fin 2) (Fin 2) F) = !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] := rfl

@[simp] theorem coe_sl2W : (sl2W F : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem sl2_ext {A B : SL2 F} (h : (A : Matrix (Fin 2) (Fin 2) F) = B) : A = B :=
  Subtype.ext h

theorem sl2U_add (c d : F) : sl2U (c + d) = sl2U c * sl2U d := by
  apply sl2_ext
  simp [Matrix.SpecialLinearGroup.coe_mul, add_comm]

theorem sl2L_add (c d : F) : sl2L (c + d) = sl2L c * sl2L d := by
  apply sl2_ext
  simp [Matrix.SpecialLinearGroup.coe_mul]

theorem sl2U_zero : sl2U (0 : F) = 1 := by
  apply sl2_ext
  simp [Matrix.one_fin_two]

theorem sl2L_zero : sl2L (0 : F) = 1 := by
  apply sl2_ext
  simp [Matrix.one_fin_two]

theorem sl2U_injective : Function.Injective (sl2U : F → SL2 F) := by
  intro c d h
  have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa using this

theorem sl2L_injective : Function.Injective (sl2L : F → SL2 F) := by
  intro c d h
  have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simpa using this

end Elements

@[expose] def SL2At {G : Type} [Group G] (H N : Subgroup G) (root : ℤ → Subgroup G) (i : ℤ) :
    Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = Nat.card (root i) ∧
    ∃ φ : SL2 F →* G, Function.Injective φ ∧ (∀ x, x ∈ root i ↔ ∃ c, φ (sl2U c) = x) ∧
      (∀ x, x ∈ root (-i) ↔ ∃ c, φ (sl2L c) = x) ∧ (∀ t : Fˣ, φ (sl2D t) ∈ H) ∧ φ (sl2W F) ∈ N

end CFSG.GH74.GLS.Stage4.Hex
