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

namespace CFSG.LargeEvenClassification.Helpers

universe actingUniverse sourceUniverse targetUniverse

@[expose] def invariantSubgroupConjugation {Acting : Type actingUniverse} [Group Acting]
    {Ambient : Type sourceUniverse} [Group Ambient] (action : Acting →* Ambient)
    (Invariant : Subgroup Ambient)
    (hstable : ∀ conjugator : Acting, ∀ element : Ambient, element ∈ Invariant →
      action conjugator * element * (action conjugator)⁻¹ ∈ Invariant) :
    Acting →* MulAut Invariant := {
  toFun := fun conjugator => {
    toFun := fun element => ⟨action conjugator * element * (action conjugator)⁻¹,
      hstable conjugator element element.property⟩
    invFun := fun element => ⟨(action conjugator)⁻¹ * element * action conjugator, by
      simpa only [map_inv, inv_inv] using hstable conjugator⁻¹ element element.property⟩
    left_inv := by intro element; apply Subtype.ext; group
    right_inv := by intro element; apply Subtype.ext; group
    map_mul' := by
      intro first second
      apply Subtype.ext
      change action conjugator * ((first : Ambient) * second) * (action conjugator)⁻¹ =
        (action conjugator * first * (action conjugator)⁻¹) *
          (action conjugator * second * (action conjugator)⁻¹)
      group }
  map_one' := by
    apply MulEquiv.ext
    intro element
    apply Subtype.ext
    change action 1 * (element : Ambient) * (action 1)⁻¹ = element
    rw [map_one]
    simp
  map_mul' := by
    intro first second
    apply MulEquiv.ext
    intro element
    apply Subtype.ext
    change action (first * second) * (element : Ambient) * (action (first * second))⁻¹ =
      action first * (action second * element * (action second)⁻¹) * (action first)⁻¹
    rw [map_mul]
    group }

theorem invariantSubgroupConjugation_apply {Acting : Type actingUniverse} [Group Acting]
    {Ambient : Type sourceUniverse} [Group Ambient] (action : Acting →* Ambient)
    (Invariant : Subgroup Ambient)
    (hstable : ∀ conjugator : Acting, ∀ element : Ambient, element ∈ Invariant →
      action conjugator * element * (action conjugator)⁻¹ ∈ Invariant)
    (conjugator : Acting) (element : Invariant) :
    (invariantSubgroupConjugation action Invariant hstable conjugator element : Ambient) =
      action conjugator * element * (action conjugator)⁻¹ := rfl

theorem pGroup_invariant_kernel_fixed_element {Acting : Type actingUniverse} [Group Acting]
    {Source : Type sourceUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ}
    (hprime : prime.Prime) (hpacting : IsPGroup prime Acting) (hpsource : IsPGroup prime Source)
    (action : Acting →* MulAut Source) (quotient : Source →* Target)
    (hinvariant : ∀ conjugator : Acting, ∀ element : Source,
      quotient element = 1 → quotient (action conjugator element) = 1)
    (hnoninjective : ¬Function.Injective quotient) :
    ∃ element : Source, element ≠ 1 ∧ quotient element = 1 ∧
      ∀ conjugator : Acting, action conjugator element = element := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : MulAction Acting quotient.ker := {
    smul := fun conjugator element =>
      ⟨action conjugator element, hinvariant conjugator element element.property⟩
    one_smul := fun element => by
      apply Subtype.ext
      change action 1 element = element
      rw [map_one]
      rfl
    mul_smul := fun first second element => by
      apply Subtype.ext
      change action (first * second) element = action first (action second element)
      rw [map_mul]
      rfl }
  have hnontrivial : quotient.ker ≠ ⊥ := by
    intro htrivial
    exact hnoninjective (quotient.ker_eq_bot_iff.mp htrivial)
  have hdivides : prime ∣ Nat.card quotient.ker := by
    rcases (hpsource.to_subgroup quotient.ker).card_eq_or_dvd with hone | hdivides
    · exact False.elim (hnontrivial (Subgroup.card_eq_one.mp hone))
    · exact hdivides
  have hidentity : (1 : quotient.ker) ∈ MulAction.fixedPoints Acting quotient.ker := by
    intro conjugator
    apply Subtype.ext
    exact map_one (action conjugator)
  obtain ⟨element, hfixed, hnonidentity⟩ :=
    hpacting.exists_fixed_point_of_prime_dvd_card_of_fixed_point quotient.ker hdivides hidentity
  refine ⟨element, ?_, element.property, ?_⟩
  · intro hone
    exact hnonidentity (Subtype.ext hone).symm
  · intro conjugator
    exact congrArg (fun entry : quotient.ker => (entry : Source)) (hfixed conjugator)

theorem pGroup_invariant_kernel_injective {Acting : Type actingUniverse} [Group Acting]
    {Source : Type sourceUniverse} [Group Source] [Finite Source]
    {Target : Type targetUniverse} [Group Target] {prime : ℕ}
    (hprime : prime.Prime) (hpacting : IsPGroup prime Acting) (hpsource : IsPGroup prime Source)
    (action : Acting →* MulAut Source) (quotient : Source →* Target)
    (hinvariant : ∀ conjugator : Acting, ∀ element : Source,
      quotient element = 1 → quotient (action conjugator element) = 1)
    (hfixedKernel : ∀ element : Source, quotient element = 1 →
      (∀ conjugator : Acting, action conjugator element = element) → element = 1) :
    Function.Injective quotient := by
  by_contra hnoninjective
  obtain ⟨element, hnonidentity, hkilled, hfixed⟩ :=
    pGroup_invariant_kernel_fixed_element hprime hpacting hpsource action quotient
      hinvariant hnoninjective
  exact hnonidentity (hfixedKernel element hkilled hfixed)

end CFSG.LargeEvenClassification.Helpers
