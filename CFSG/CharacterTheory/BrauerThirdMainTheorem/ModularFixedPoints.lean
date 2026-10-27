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
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem pGroup_representation_exists_fixed (prime : ℕ) (hprime : prime.Prime)
    (G : Type*) [Group G] [Finite G] (hpGroup : IsPGroup prime G)
    (field : Type*) [Field field] [CharP field prime]
    (space : Type*) [AddCommGroup space] [Module field space] [Nontrivial space]
    (representation : Representation field G space) :
    ∃ vector : space, vector ≠ 0 ∧ ∀ element : G, representation element vector = vector := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : Algebra (ZMod prime) field := ZMod.algebra field prime
  let : Module (ZMod prime) space := Module.compHom space (algebraMap (ZMod prime) field)
  let : IsScalarTower (ZMod prime) field space := IsScalarTower.of_algebraMap_smul
    (fun _ _ => rfl)
  obtain ⟨base, hbase⟩ := exists_ne (0 : space)
  let orbitSpan : Submodule (ZMod prime) space :=
    Submodule.span (ZMod prime) (Set.range (fun element : G => representation element base))
  let : Module.Finite (ZMod prime) orbitSpan := Module.Finite.span_of_finite _ (Set.finite_range _)
  let : Finite orbitSpan := Module.finite_of_finite (ZMod prime)
  have hbaseMem : base ∈ orbitSpan := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  have hstable (element : G) : ∀ vector ∈ orbitSpan, representation element vector ∈ orbitSpan := by
    intro vector hvector
    let restricted := (representation element).restrictScalars (ZMod prime)
    have hmap : Submodule.map restricted orbitSpan ≤ orbitSpan := by
      rw [Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨factor, rfl⟩, rfl⟩
      change representation element (representation factor base) ∈ orbitSpan
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨element * factor, rfl⟩
    exact (Submodule.map_le_iff_le_comap.mp hmap) hvector
  let : MulAction G orbitSpan := {
    smul element vector := ⟨representation element vector.val, hstable element vector.val vector.property⟩
    one_smul vector := by
      apply Subtype.ext
      change representation 1 vector.val = vector.val
      simp
    mul_smul left right vector := by
      apply Subtype.ext
      change representation (left * right) vector.val =
        representation left (representation right vector.val)
      rw [map_mul, Module.End.mul_apply]
  }
  have hnonzeroBase : (⟨base, hbaseMem⟩ : orbitSpan) ≠ 0 := by
    intro hequal
    exact hbase (congrArg Subtype.val hequal)
  let : Nontrivial orbitSpan := ⟨⟨_, _, hnonzeroBase⟩⟩
  have hdimension : 0 < Module.finrank (ZMod prime) orbitSpan := Module.finrank_pos
  have hdivides : prime ∣ Nat.card orbitSpan := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod prime),
      Nat.card_eq_fintype_card (α := ZMod prime), ZMod.card prime]
    exact dvd_pow_self prime (Nat.ne_of_gt hdimension)
  have hzeroFixed : (0 : orbitSpan) ∈ MulAction.fixedPoints G orbitSpan := by
    rw [MulAction.mem_fixedPoints]
    intro element
    exact Subtype.ext (map_zero (representation element))
  obtain ⟨vector, hfixed, hnonzero⟩ :=
    hpGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point orbitSpan hdivides hzeroFixed
  refine ⟨vector.val, ?_, ?_⟩
  · intro hequal
    exact hnonzero (Subtype.ext hequal).symm
  · intro element
    exact congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hfixed) element)

theorem normalPSubgroup_irreducible_trivial (prime : ℕ) (hprime : prime.Prime)
    (G : Type*) [Group G] (subgroup : Subgroup G) [subgroup.Normal] [Finite subgroup]
    (hpGroup : IsPGroup prime subgroup) (field : Type*) [Field field] [CharP field prime]
    (space : Type*) [AddCommGroup space] [Module field space]
    (representation : Representation field G space) [representation.IsIrreducible] :
    ∀ element : subgroup, representation element.val = LinearMap.id := by
  classical
  let : Nontrivial space := by
    let : Nontrivial representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra field G) representation.asModule
    exact representation.asModuleEquiv.toEquiv.symm.nontrivial
  obtain ⟨vector, hnonzero, hfixed⟩ := pGroup_representation_exists_fixed prime hprime subgroup hpGroup
    field space (representation.comp subgroup.subtype)
  let invariant : Subrepresentation representation := {
    toSubmodule := Representation.invariants (representation.comp subgroup.subtype)
    apply_mem_toSubmodule element := representation.le_comap_invariants subgroup element
  }
  have hvector : vector ∈ invariant.toSubmodule :=
    (Representation.mem_invariants _ _).mpr hfixed
  have hnotBot : invariant ≠ ⊥ := by
    intro hequal
    have hequalSubmodule := congrArg Subrepresentation.toSubmodule hequal
    rw [hequalSubmodule] at hvector
    exact hnonzero hvector
  have htop : invariant = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top invariant).resolve_left hnotBot
  intro element
  apply LinearMap.ext
  intro candidate
  have hmember : candidate ∈ invariant.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  exact (Representation.mem_invariants _ _).mp hmember element

end CFSG.BrauerThirdMainTheorem.Helpers
