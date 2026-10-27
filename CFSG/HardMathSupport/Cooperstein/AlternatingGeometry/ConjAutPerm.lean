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

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

theorem exists_conj_of_autM {M : Type*} [Group M] [Finite M] {Ω : Type*} [Fintype Ω]
    [DecidableEq Ω]
    (hAut : ∀ φ : Perm Ω ≃* Perm Ω, ∃ g : Perm Ω, ∀ x, φ x = g * x * g⁻¹)
    (θ : M →* Perm Ω) (hθ : Function.Surjective θ) (α : M ≃* M)
    (hα : ∀ m, θ m = 1 → θ (α m) = 1) :
    ∃ g : Perm Ω, ∀ m, θ (α m) = g * θ m * g⁻¹ := by
  classical
  let θ' : M →* Perm Ω := θ.comp α.toMonoidHom
  have hker : θ.ker ≤ θ'.ker := fun m hm => hα m hm
  let β : Perm Ω →* Perm Ω :=
    θ.liftOfRightInverse (Function.surjInv hθ) (Function.rightInverse_surjInv hθ) ⟨θ', hker⟩
  have hβ : ∀ m, β (θ m) = θ (α m) := fun m =>
    MonoidHom.liftOfRightInverse_comp_apply θ (Function.surjInv hθ)
      (Function.rightInverse_surjInv hθ) ⟨θ', hker⟩ m
  have hsurj : Function.Surjective β := by
    intro p
    obtain ⟨m, rfl⟩ := hθ p
    obtain ⟨m', rfl⟩ := α.surjective m
    exact ⟨θ m', hβ m'⟩
  have hinj : Function.Injective β := Finite.injective_iff_surjective.2 hsurj
  obtain ⟨g, hg⟩ := hAut (MulEquiv.ofBijective β ⟨hinj, hsurj⟩)
  exact ⟨g, fun m => by rw [← hβ]; exact hg (θ m)⟩

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
