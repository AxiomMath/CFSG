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
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.AS35Z

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
theorem injective_of_commute (D : Set (Module.End (ZMod 2) V))
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ d ∈ D, ∀ w ∈ W, d w ∈ W) → W = ⊥ ∨ W = ⊤)
    {f : Module.End (ZMod 2) V} (hf : ∀ d ∈ D, d * f = f * d) (hf0 : f ≠ 0) :
    Function.Injective f := by
  rcases hirr (LinearMap.ker f) (fun d hd w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      have := congrArg (fun g : Module.End (ZMod 2) V => g w) (hf d hd)
      simp only [Module.End.mul_apply, hw, map_zero] at this
      exact this.symm) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exfalso
    apply hf0
    ext v
    have : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simpa using this

theorem eq_or_eq_sq_of_commute [Nontrivial V] (D : Set (Module.End (ZMod 2) V))
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ d ∈ D, ∀ w ∈ W, d w ∈ W) → W = ⊥ ∨ W = ⊤)
    {J J' : Module.End (ZMod 2) V} (hJ : ∀ d ∈ D, d * J = J * d)
    (hJ' : ∀ d ∈ D, d * J' = J' * d) (hJ3 : J * J + J + 1 = 0) (hJ'3 : J' * J' + J' + 1 = 0) :
    J' = J ∨ J' = J * J := by
  set E := Subalgebra.centralizer (ZMod 2) D with hE
  have hmemE : ∀ f : Module.End (ZMod 2) V, (∀ d ∈ D, d * f = f * d) → f ∈ E := by
    intro f hf
    rw [hE, Subalgebra.mem_centralizer_iff]
    exact hf
  have hcomm : ∀ f ∈ E, ∀ d ∈ D, d * f = f * d := by
    intro f hf d hd
    rw [hE, Subalgebra.mem_centralizer_iff] at hf
    exact hf d hd
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have : NoZeroDivisors E := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    have ha := injective_of_commute D hirr (hcomm a a.2)
      (fun h0 => hne.1 (Subtype.ext h0))
    have hb := injective_of_commute D hirr (hcomm b b.2)
      (fun h0 => hne.2 (Subtype.ext h0))
    have hab' : (a : Module.End (ZMod 2) V) * b = 0 := congrArg Subtype.val hab
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : (a : Module.End (ZMod 2) V) ((b : Module.End (ZMod 2) V) v) = 0 := by
      rw [← Module.End.mul_apply, hab']
      rfl
    exact hv (hb (by rw [map_zero]; exact ha (by rw [map_zero]; exact h1)))
  have : IsDomain E := NoZeroDivisors.to_isDomain E
  have hfield := Finite.isDomain_to_isField E
  have hJE := hmemE J hJ
  have hJ'E := hmemE J' hJ'
  let _ : CommRing E := { (inferInstance : Ring E) with mul_comm := hfield.mul_comm }
  set j : E := ⟨J, hJE⟩ with hj
  set j' : E := ⟨J', hJ'E⟩ with hj'
  have hj3 : j * j + j + 1 = 0 := Subtype.ext (by simpa [hj] using hJ3)
  have hj'3 : j' * j' + j' + 1 = 0 := Subtype.ext (by simpa [hj'] using hJ'3)
  have hprod : (j' - j) * (j' - j * j) = 0 := by
    linear_combination hj'3 + (j - 1 - j') * hj3
  rcases mul_eq_zero.1 hprod with h0 | h0
  · left
    exact congrArg Subtype.val (sub_eq_zero.1 h0)
  · right
    exact congrArg Subtype.val (sub_eq_zero.1 h0)

end CFSG.LargeExtraspecial.AS35Z
