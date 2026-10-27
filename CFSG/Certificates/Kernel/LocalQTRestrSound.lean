module

public import CFSG.Certificates.Kernel.Spor.PEnumSound
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

namespace CFSG.KC.Restr

open CFSG.PSL3Four.Native

variable {α : Type*}

@[expose] def stabP (S : Set α) : Subgroup (Equiv.Perm α) where
  carrier := {g | ∀ x, g x ∈ S ↔ x ∈ S}
  mul_mem' {g h} hg hh x := by
    simp only [Set.mem_ofPred_eq] at hg hh
    rw [Equiv.Perm.mul_apply, hg, hh]
  one_mem' _ := Iff.rfl
  inv_mem' {g} hg x := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [← hg (g⁻¹ x)]
    simp

theorem mem_stabP {S : Set α} {g : Equiv.Perm α} : g ∈ stabP S ↔ ∀ x, g x ∈ S ↔ x ∈ S :=
  Iff.rfl

theorem mem_stabP_of_mapsTo [Finite α] {S : Set α} {g : Equiv.Perm α} (h : ∀ x ∈ S, g x ∈ S) :
    g ∈ stabP S := by
  intro x
  refine ⟨fun hx => ?_, h x⟩
  let r : S → S := fun y => ⟨g y, h y y.2⟩
  have hr : Function.Injective r := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hr) ⟨g x, hx⟩
  have e : g y = g x := congrArg Subtype.val hy
  rw [← g.injective e]
  exact y.2

@[expose] def resHom (S : Set α) : stabP S →* Equiv.Perm S where
  toFun g := (g : Equiv.Perm α).subtypePerm (fun x => mem_stabP.1 g.2 x)
  map_one' := by
    ext
    rfl
  map_mul' _ _ := by
    ext
    rfl

theorem resHom_apply (S : Set α) (g : stabP S) (x : S) :
    ((resHom S g x : S) : α) = (g : Equiv.Perm α) x := rfl

theorem posOf_eq {A : Array Tab} (hA : A.toList.Nodup) {k : ℕ} (hk : k < A.size) :
    posOf (indexOf A) A A[k]! = k := by
  have hf := (CFSG.KS.PEnum.found_indexOf_iff A A[k]!).2 ⟨k, hk, rfl⟩
  unfold found at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
  obtain ⟨h1, h2⟩ := hf
  generalize posOf (indexOf A) A A[k]! = p at h1 h2 ⊢
  rw [getElem!_pos A p h1, getElem!_pos A k hk] at h2
  exact (List.Nodup.getElem_inj_iff hA (i := p) (j := k) (hi := by simpa using h1)
    (hj := by simpa using hk)).1 (by simpa using h2)

end CFSG.KC.Restr

end
