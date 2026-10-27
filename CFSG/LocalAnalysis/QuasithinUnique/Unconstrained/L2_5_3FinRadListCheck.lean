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

namespace CFSG.QuasithinUnique.Fin253

@[expose] def lpow {ι : Type} (mul : ι → ι → ι) (one : ι) (y : ι) : ℕ → ι
  | 0 => one
  | n + 1 => mul y (lpow mul one y n)

structure ListModel (X ι : Type) [Group X] where
  enc : X → ι
  inj : Function.Injective enc
  mul : ι → ι → ι
  one : ι
  inv : ι → ι
  enc_mul : ∀ x y : X, enc (x * y) = mul (enc x) (enc y)
  enc_one : enc 1 = one
  enc_inv : ∀ x : X, enc x⁻¹ = inv (enc x)
  elems : List ι
  mem_elems : ∀ y : ι, y ∈ elems ↔ ∃ x : X, enc x = y

@[expose] def ListModel.ofMulEquiv {X Y ι : Type} [Group X] [Group Y] (M : ListModel X ι)
    (e : Y ≃* X) : ListModel Y ι where
  enc := fun y => M.enc (e y)
  inj := fun a b h => e.injective (M.inj h)
  mul := M.mul
  one := M.one
  inv := M.inv
  enc_mul := fun x y => by simp only [map_mul, M.enc_mul]
  enc_one := by simp only [map_one, M.enc_one]
  enc_inv := fun x => by simp only [map_inv, M.enc_inv]
  elems := M.elems
  mem_elems := fun y => by
    rw [M.mem_elems]
    exact ⟨fun ⟨x, hx⟩ => ⟨e.symm x, by simpa using hx⟩, fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩

section Checks

variable {ι : Type} [DecidableEq ι]

@[expose] def QuatOK (mul : ι → ι → ι) (one t : ι) (S : List ι) : Prop :=
  S ≠ [] ∧ (∀ y ∈ S, ∀ y' ∈ S, mul y y' = one ∨ mul y y' = t ∨ mul (mul y y') (mul y y') = t) ∧
    (one :: t :: S).Nodup ∧ 5 ≤ (one :: t :: S).length

instance (mul : ι → ι → ι) (one t : ι) (S : List ι) : Decidable (QuatOK mul one t S) := by
  unfold QuatOK
  infer_instance

@[expose] def CoreOK (mul : ι → ι → ι) (one : ι) (inv : ι → ι) (t : ι) (C : List ι) : Prop :=
  ∀ c ∈ C, (c = one ∨ c = t ∨ mul c c = t) ∨
    ∃ w ∈ C, lpow mul one (mul (inv c) (mul (mul w c) (inv w))) 16 ≠ one

instance (mul : ι → ι → ι) (one : ι) (inv : ι → ι) (t : ι) (C : List ι) :
    Decidable (CoreOK mul one inv t C) := by
  unfold CoreOK
  infer_instance

@[expose] def CenterOK (mul : ι → ι → ι) (one : ι) (elems : List ι) : Prop :=
  ∀ z ∈ elems, z = one ∨ ∃ x ∈ elems, mul z x ≠ mul x z

instance (mul : ι → ι → ι) (one : ι) (elems : List ι) : Decidable (CenterOK mul one elems) := by
  unfold CenterOK
  infer_instance

@[expose] def OddOK (mul : ι → ι → ι) (one : ι) (m : ℕ) (elems invs ord4 : List ι) : Prop :=
  ∀ x ∈ elems, x ≠ one → lpow mul one x m = one →
    (∀ u ∈ ord4, mul u x ≠ mul x u) ∧
    ∀ t ∈ invs.filter (fun t => decide (mul t x = mul x t)),
      ∀ s ∈ invs.filter (fun s => decide (mul s x = mul x s)),
        t ≠ s → mul t s = mul s t → False

instance (mul : ι → ι → ι) (one : ι) (m : ℕ) (elems invs ord4 : List ι) :
    Decidable (OddOK mul one m elems invs ord4) := by
  unfold OddOK
  infer_instance

@[expose] def QuatAll (mul : ι → ι → ι) (one : ι) (elems invs : List ι) : Prop :=
  ∀ t ∈ invs, QuatOK mul one t (elems.filter fun y => decide (mul y y = t))

instance (mul : ι → ι → ι) (one : ι) (elems invs : List ι) : Decidable (QuatAll mul one elems invs) := by
  unfold QuatAll
  infer_instance

@[expose] def CoreAll (mul : ι → ι → ι) (one : ι) (inv : ι → ι) (elems invs : List ι) : Prop :=
  ∀ t ∈ invs, CoreOK mul one inv t (elems.filter fun c => decide (mul c t = mul t c))

instance (mul : ι → ι → ι) (one : ι) (inv : ι → ι) (elems invs : List ι) :
    Decidable (CoreAll mul one inv elems invs) := by
  unfold CoreAll
  infer_instance

end Checks

end CFSG.QuasithinUnique.Fin253
