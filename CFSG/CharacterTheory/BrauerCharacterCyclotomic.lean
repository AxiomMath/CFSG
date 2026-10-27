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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

namespace BrauerCharacterCyclotomic

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  classical
  let n := Monoid.exponent G
  have hn : n ≠ 0 := Monoid.exponent_ne_zero_of_finite
  let : NeZero n := ⟨hn⟩
  let : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr hn⟩
  let : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  let φ : CyclotomicField n ℚ →+* ℂ := Classical.choice inferInstance
  let ψ : CyclotomicField n ℚ →ₐ[ℚ] ℂ := φ.toRatAlgHom
  refine ⟨φ, ?_⟩
  intro V _ _ _ ρ g
  let f : Module.End ℂ V := ρ g
  have hρ : f ^ n = 1 := by
    dsimp [f]
    rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]
  let : IsCyclotomicExtension {n} ℚ (↥ψ.range) := by
    change IsCyclotomicExtension {n} ℚ ψ.fieldRange
    exact IsCyclotomicExtension.equiv {n} ℚ (CyclotomicField n ℚ) ψ.equivFieldRange
  have hsum : f.charpoly.roots.sum ∈ ψ.range := by
    apply Subalgebra.multiset_sum_mem
    intro μ hμ
    have heig : f.HasEigenvalue μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2
        (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hμpow : μ ^ n = 1 := by
      apply smul_left_injective ℂ hv.2
      simpa [hρ] using (Module.End.HasEigenvector.pow_apply hv n).symm
    exact IsCyclotomicExtension.mem_of_pow_eq_one {n} ψ.range (by simp) hn hμpow
  change LinearMap.trace ℂ V f ∈ φ.range
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  simpa [ψ] using hsum

end BrauerCharacterCyclotomic

end CFSG
