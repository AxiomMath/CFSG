module

public import CFSG.Mathlib.GroupTheory.Basic
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
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.TwoRankLowerBound.Helpers

theorem involutive_linearMap_eq_one_of_trace_eq_finrank {field vector : Type*}
    [Field field] [CharZero field] [AddCommGroup vector] [Module field vector]
    [FiniteDimensional field vector] (endomorphism : Module.End field vector)
    (hsquare : endomorphism * endomorphism = 1)
    (htrace : LinearMap.trace field vector endomorphism = Module.finrank field vector) :
    endomorphism = 1 := by
  let projection : Module.End field vector := (2 : field)⁻¹ • (1 - endomorphism)
  have hproduct : (1 - endomorphism) * (1 - endomorphism) =
      (2 : field) • (1 - endomorphism) := by
    calc
      (1 - endomorphism) * (1 - endomorphism) =
          1 - endomorphism - endomorphism + endomorphism * endomorphism := by noncomm_ring
      _ = (2 : field) • (1 - endomorphism) := by rw [hsquare]; module
  have hidempotent : IsIdempotentElem projection := by
    change projection * projection = projection
    dsimp [projection]
    rw [smul_mul_assoc, mul_smul_comm, hproduct, smul_smul, smul_smul]
    congr 1
    field_simp
  have hprojectiontrace : LinearMap.trace field vector projection = 0 := by
    dsimp [projection]
    rw [map_smul, map_sub, LinearMap.trace_one, htrace, sub_self, smul_zero]
  have hprojectionzero := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero
    hidempotent hprojectiontrace
  have hdifference : (1 : Module.End field vector) - endomorphism = 0 := by
    have hscaled := congrArg (fun operator : Module.End field vector => (2 : field) • operator)
      hprojectionzero
    dsimp [projection] at hscaled
    simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (2 : field) ≠ 0), one_smul,
      smul_zero] using hscaled
  exact (sub_eq_zero.mp hdifference).symm

theorem representation_involution_eq_one_of_character_eq_degree {G vector : Type*}
    [Group G] [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) (involution : G)
    (hsquare : involution ^ 2 = 1)
    (hcharacter : representation.character involution = representation.character 1) :
    representation involution = 1 := by
  apply involutive_linearMap_eq_one_of_trace_eq_finrank
  · rw [← map_mul, ← pow_two, hsquare, map_one]
  · change LinearMap.trace ℂ vector (representation involution) =
      (Module.finrank ℂ vector : ℂ)
    rw [Representation.char_one] at hcharacter
    exact hcharacter

theorem representation_proper_kernel_contains_involution_of_character_eq_degree
    {G vector : Type*} [Group G] [AddCommGroup vector] [Module ℂ vector]
    [FiniteDimensional ℂ vector] (representation : Representation ℂ G vector)
    (hnontrivial : ∃ element : G, representation element ≠ 1) (involution : G)
    (hsquare : involution ^ 2 = 1)
    (hcharacter : representation.character involution = representation.character 1) :
    representation.ker ≠ ⊤ ∧ involution ∈ representation.ker := by
  constructor
  · intro htop
    obtain ⟨element, hnontrivial⟩ := hnontrivial
    apply hnontrivial
    apply MonoidHom.mem_ker.mp
    rw [htop]
    trivial
  · exact representation_involution_eq_one_of_character_eq_degree representation involution
      hsquare hcharacter

theorem representation_involution_character_ne_degree_of_simple {G vector : Type*}
    [Group G] [IsSimpleGroup G] [AddCommGroup vector] [Module ℂ vector]
    [FiniteDimensional ℂ vector] (representation : Representation ℂ G vector)
    (hnontrivial : ∃ element : G, representation element ≠ 1) (involution : G)
    (horder : orderOf involution = 2) :
    representation.character involution ≠ representation.character 1 := by
  intro hcharacter
  obtain ⟨hproper, hmember⟩ :=
    representation_proper_kernel_contains_involution_of_character_eq_degree representation
      hnontrivial involution (orderOf_eq_prime_iff.mp horder).1 hcharacter
  obtain hbot | htop := CFSG.eq_bot_or_eq_top_of_normal representation.ker inferInstance
  · rw [hbot, Subgroup.mem_bot] at hmember
    exact (orderOf_eq_prime_iff.mp horder).2 hmember
  · exact hproper htop

end CFSG.TwoRankLowerBound.Helpers
