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

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def functionSubringEvaluation {coefficient index : Type*} [CommRing coefficient]
    (ring : Subring (index → coefficient)) (coordinate : index) : ring →+* coefficient :=
  (Pi.evalRingHom (fun _ : index => coefficient) coordinate).comp ring.subtype

theorem finite_function_prime_ideal_contains_evaluation_kernel {coefficient index : Type*}
    [CommRing coefficient] [Fintype index] [Nonempty index]
    (ring : Subring (index → coefficient)) (ideal : Ideal ring) [ideal.IsPrime] :
    ∃ coordinate : index, RingHom.ker (functionSubringEvaluation ring coordinate) ≤ ideal := by
  by_contra hnot
  have hexists : ∀ coordinate : index,
      ∃ function : ring, function ∈ RingHom.ker (functionSubringEvaluation ring coordinate) ∧
        function ∉ ideal := by
    intro coordinate
    have hnotLe : ¬RingHom.ker (functionSubringEvaluation ring coordinate) ≤ ideal :=
      fun hle => hnot ⟨coordinate, hle⟩
    exact Set.not_subset.mp hnotLe
  choose function hkernel houtside using hexists
  have hproduct : (∏ coordinate : index, function coordinate) = 0 := by
    apply Subtype.ext
    funext coordinate
    change (ring.subtype (∏ member : index, function member)) coordinate = (0 : index → coefficient) coordinate
    rw [map_prod]
    rw [Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    exact RingHom.mem_ker.mp (hkernel coordinate)
  have hmember : (∏ coordinate : index, function coordinate) ∈ ideal := by
    rw [hproduct]
    exact ideal.zero_mem
  obtain ⟨coordinate, _, hinside⟩ := Ideal.IsPrime.prod_mem_iff.mp hmember
  exact houtside coordinate hinside

theorem finite_function_subring_maximal_ideal {coefficient index : Type*}
    [CommRing coefficient] [Fintype index] [Nonempty index]
    (ring : Subring (index → coefficient))
    (hconstants : ∀ value : coefficient, (fun _ : index => value) ∈ ring)
    (ideal : Ideal ring) [ideal.IsMaximal] :
    ∃ (coordinate : index) (residueIdeal : Ideal coefficient), residueIdeal.IsMaximal ∧
      ideal = Ideal.comap (functionSubringEvaluation ring coordinate) residueIdeal := by
  obtain ⟨coordinate, hkernel⟩ := finite_function_prime_ideal_contains_evaluation_kernel ring ideal
  let evaluation := functionSubringEvaluation ring coordinate
  have hsurjective : Function.Surjective evaluation := by
    intro value
    exact ⟨⟨fun _ => value, hconstants value⟩, rfl⟩
  have hcomap : Ideal.comap evaluation (Ideal.map evaluation ideal) = ideal := by
    rw [Ideal.comap_map_of_surjective' evaluation hsurjective, sup_eq_left.mpr hkernel]
  have hproper : Ideal.map evaluation ideal ≠ ⊤ := by
    intro htop
    rw [htop, Ideal.comap_top] at hcomap
    exact (inferInstance : ideal.IsMaximal).ne_top hcomap.symm
  obtain htop | hmaximal := Ideal.map_eq_top_or_isMaximal_of_surjective evaluation hsurjective
    (inferInstance : ideal.IsMaximal)
  · exact False.elim (hproper htop)
  · exact ⟨coordinate, Ideal.map evaluation ideal, hmaximal, hcomap.symm⟩

end CFSG.TwoRankLowerBound.Helpers
