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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.LittleWedderburn
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

open scoped commutatorElement

namespace CFSG.AGLEmbeddingD2.McLaughlin

theorem eq_one_of_perfect_of_simple {k W A Γ : Type*} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [Module.Finite k W] [Monoid A] [Group Γ]
    (ρ : A →* Module.End k W) (σ : Γ →* Module.End k W)
    (hsimple : ∀ U : Submodule k W, (∀ a, ∀ w ∈ U, ρ a w ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcomm : ∀ (g : Γ) (a : A), σ g * ρ a = ρ a * σ g)
    (hΓ : commutator Γ = ⊤) (g : Γ) : σ g = 1 := by
  classical
  have hinj : ∀ f : Module.End k W, (∀ c : A, ρ c * f = f * ρ c) → f ≠ 0 →
      Function.Injective f := by
    intro f hf hne
    have hinv : ∀ c : A, ∀ w ∈ LinearMap.ker f, ρ c w ∈ LinearMap.ker f := by
      intro c w hw
      rw [LinearMap.mem_ker] at hw ⊢
      have h := congrArg (fun T : Module.End k W => T w) (hf c)
      simp only [Module.End.mul_apply] at h
      rw [← h, hw, map_zero]
    rcases hsimple _ hinv with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact absurd (LinearMap.ker_eq_top.mp h) hne
  let D : Subalgebra k (Module.End k W) := Subalgebra.centralizer k (Set.range ρ)
  have hmemD : ∀ f : Module.End k W, f ∈ D ↔ ∀ c : A, ρ c * f = f * ρ c := by
    intro f
    constructor
    · intro hf c
      exact (Subalgebra.mem_centralizer_iff (R := k)).mp hf (ρ c) ⟨c, rfl⟩
    · intro hf
      exact (Subalgebra.mem_centralizer_iff (R := k)).mpr (by rintro _ ⟨c, rfl⟩; exact hf c)
  have hσD : ∀ x : Γ, σ x ∈ D := fun x => (hmemD _).mpr fun c => (hcomm x c).symm
  have hcommute : ∀ x y : Γ, σ x * σ y = σ y * σ x := by
    rcases subsingleton_or_nontrivial (Module.End k W) with hW | hW
    · intro x y
      exact Subsingleton.elim _ _
    · have : Nontrivial D :=
        ⟨⟨⟨0, D.zero_mem⟩, ⟨1, D.one_mem⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
      have : NoZeroDivisors D := ⟨fun {a b} hab => by
        by_cases ha : (a : Module.End k W) = 0
        · exact Or.inl (Subtype.ext ha)
        · right
          apply Subtype.ext
          have hab' : (a : Module.End k W) * (b : Module.End k W) = 0 := by
            simpa using congrArg Subtype.val hab
          have hai := hinj (a : Module.End k W) ((hmemD _).mp a.2) ha
          apply LinearMap.ext
          intro w
          apply hai
          have h := congrArg (fun T : Module.End k W => T w) hab'
          simpa using h⟩
      have : IsDomain D := NoZeroDivisors.to_isDomain D
      have : Module.Finite k (Module.End k W) := inferInstance
      have : Finite (Module.End k W) := Module.finite_of_finite k
      have : Finite D := Subtype.finite
      let : Field D := (Finite.isDomain_to_isField D).toField
      intro x y
      exact congrArg Subtype.val (mul_comm (⟨σ x, hσD x⟩ : D) ⟨σ y, hσD y⟩)
  have hker : commutator Γ ≤ σ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    have hx : σ x * σ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hy : σ y * σ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hcommute x y, mul_assoc (σ y) (σ x) (σ x⁻¹), hx, mul_one, hy]
  rw [hΓ] at hker
  exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top g))

end CFSG.AGLEmbeddingD2.McLaughlin

end
