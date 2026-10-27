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
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem alternating_form_has_nondegenerate_plane
    {coefficient : Type u} {space : Type v}
    [Field coefficient] [AddCommGroup space] [Module coefficient space]
    [FiniteDimensional coefficient space]
    (form : LinearMap.BilinForm coefficient space) (halt : form.IsAlt)
    (first second : space) (hnonzero : form first second ≠ 0) :
    ∃ plane : Submodule coefficient space,
      Module.finrank coefficient plane = 2 ∧ (form.restrict plane).Nondegenerate := by
  let embed : coefficient × coefficient →ₗ[coefficient] space :=
    (LinearMap.fst coefficient coefficient coefficient).smulRight first +
      (LinearMap.snd coefficient coefficient coefficient).smulRight second
  have hembed : ∀ scalar : coefficient × coefficient,
      embed scalar = scalar.1 • first + scalar.2 • second := fun _ => rfl
  have hreverse : form second first = -form first second := (halt.neg_eq first second).symm
  have hfirst : ∀ scalar : coefficient × coefficient,
      form (embed scalar) second = scalar.1 * form first second := by
    intro scalar
    rw [hembed, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_left, halt.self_eq_zero, mul_zero, add_zero]
  have hsecond : ∀ scalar : coefficient × coefficient,
      form (embed scalar) first = scalar.2 * (-form first second) := by
    intro scalar
    rw [hembed, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_left, halt.self_eq_zero, mul_zero, zero_add, hreverse]
  have hinjective : Function.Injective embed := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro scalar hzero
    have hfirstZero : scalar.1 = 0 := by
      have hequal := hfirst scalar
      rw [hzero, LinearMap.BilinForm.zero_left] at hequal
      exact (mul_eq_zero.mp hequal.symm).resolve_right hnonzero
    have hsecondZero : scalar.2 = 0 := by
      have hequal := hsecond scalar
      rw [hzero, LinearMap.BilinForm.zero_left] at hequal
      exact (mul_eq_zero.mp hequal.symm).resolve_right (neg_ne_zero.mpr hnonzero)
    exact Prod.ext hfirstZero hsecondZero
  have hfirstMem : first ∈ embed.range := by
    refine ⟨(1, 0), ?_⟩
    simp only [hembed, one_smul, zero_smul, add_zero]
  have hsecondMem : second ∈ embed.range := by
    refine ⟨(0, 1), ?_⟩
    simp only [hembed, one_smul, zero_smul, zero_add]
  have hleft : ∀ member : embed.range,
      (∀ other : embed.range, (form.restrict embed.range) member other = 0) → member = 0 := by
    intro member hfixed
    obtain ⟨scalar, hscalar⟩ := member.property
    have hfirstZero : scalar.1 = 0 := by
      have hequal := hfixed ⟨second, hsecondMem⟩
      change form member.val second = 0 at hequal
      rw [← hscalar, hfirst] at hequal
      exact (mul_eq_zero.mp hequal).resolve_right hnonzero
    have hsecondZero : scalar.2 = 0 := by
      have hequal := hfixed ⟨first, hfirstMem⟩
      change form member.val first = 0 at hequal
      rw [← hscalar, hsecond] at hequal
      exact (mul_eq_zero.mp hequal).resolve_right (neg_ne_zero.mpr hnonzero)
    apply Subtype.ext
    rw [← hscalar, hembed, hfirstZero, hsecondZero, zero_smul, zero_smul, add_zero]
    rfl
  have haltRestricted : (form.restrict embed.range).IsAlt := fun member => halt member.val
  refine ⟨embed.range, ?_, ⟨hleft, ?_⟩⟩
  · rw [LinearMap.finrank_range_of_inj hinjective, Module.finrank_prod]
    simp
  · intro member hfixed
    apply hleft
    intro other
    exact haltRestricted.eq_iff.mpr (hfixed other)

theorem alternating_nondegenerate_form_finrank_even
    {coefficient : Type u} {space : Type v}
    [Field coefficient] [AddCommGroup space] [Module coefficient space]
    [FiniteDimensional coefficient space]
    (form : LinearMap.BilinForm coefficient space) (halt : form.IsAlt)
    (hnondegenerate : form.Nondegenerate) : Even (Module.finrank coefficient space) := by
  have allDimensions : ∀ dimension : ℕ,
      ∀ (carrier : Type v) [AddCommGroup carrier] [Module coefficient carrier]
        [FiniteDimensional coefficient carrier],
        Module.finrank coefficient carrier = dimension →
          ∀ pairing : LinearMap.BilinForm coefficient carrier,
            pairing.IsAlt → pairing.Nondegenerate → Even dimension := by
    intro dimension
    induction dimension using Nat.strong_induction_on with
    | h dimension hinduction =>
      intro carrier _ _ _ hdimension pairing hpairingAlt hpairingNondegenerate
      by_cases hzero : dimension = 0
      · rw [hzero]
        exact ⟨0, rfl⟩
      have hpositive : 0 < Module.finrank coefficient carrier := by omega
      obtain ⟨first, hfirst⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpositive
      have hexists : ∃ second : carrier, pairing first second ≠ 0 := by
        by_contra hnone
        push Not at hnone
        exact hfirst (hpairingNondegenerate.1 first hnone)
      obtain ⟨second, hsecond⟩ := hexists
      obtain ⟨plane, hplaneRank, hplaneNondegenerate⟩ :=
        alternating_form_has_nondegenerate_plane pairing hpairingAlt first second hsecond
      have hcompl : IsCompl plane (pairing.orthogonal plane) :=
        LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
          hpairingAlt.isRefl hplaneNondegenerate
      have hcomplementDisjoint : Disjoint (pairing.orthogonal plane)
          (pairing.orthogonal (pairing.orthogonal plane)) := by
        rw [LinearMap.BilinForm.orthogonal_orthogonal hpairingNondegenerate hpairingAlt.isRefl]
        exact hcompl.disjoint.symm
      have hcomplementNondegenerate : (pairing.restrict (pairing.orthogonal plane)).Nondegenerate :=
        pairing.nondegenerate_restrict_of_disjoint_orthogonal hpairingAlt.isRefl hcomplementDisjoint
      have hcomplementAlt : (pairing.restrict (pairing.orthogonal plane)).IsAlt :=
        fun member => hpairingAlt member.val
      have hrank := Submodule.finrank_add_eq_of_isCompl hcompl
      rw [hplaneRank, hdimension] at hrank
      have hless : Module.finrank coefficient (pairing.orthogonal plane) < dimension := by omega
      have heven := hinduction _ hless (pairing.orthogonal plane) rfl
        (pairing.restrict (pairing.orthogonal plane)) hcomplementAlt hcomplementNondegenerate
      obtain ⟨width, hwidth⟩ := heven
      refine ⟨width + 1, ?_⟩
      omega
  exact allDimensions (Module.finrank coefficient space) space rfl form halt hnondegenerate

end CFSG.PreuniquenessRankFour.Helpers
