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

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem map_generated_subgroup {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (homomorphism : Source →* Target)
    (generators : Set Source) :
    (Subgroup.closure generators).map homomorphism =
      Subgroup.closure (homomorphism '' generators) := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro element helement
    exact Subgroup.subset_closure ⟨element, helement, rfl⟩
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨element, helement, rfl⟩
    exact Subgroup.mem_map.mpr ⟨element, Subgroup.subset_closure helement, rfl⟩

theorem extension_generators {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) (kernelGenerators : Finset quotient.ker)
    (imageGenerators : Finset Target)
    (hkernel : Subgroup.closure (kernelGenerators : Set quotient.ker) = ⊤)
    (himage : Subgroup.closure (imageGenerators : Set Target) = ⊤) :
    ∃ generators : Finset Source,
      Subgroup.closure (generators : Set Source) = ⊤ ∧
        generators.card ≤ kernelGenerators.card + imageGenerators.card := by
  classical
  let lift := fun element => Classical.choose (hsurjective element)
  have hlift : ∀ element, quotient (lift element) = element := by
    intro element
    exact Classical.choose_spec (hsurjective element)
  let generators := kernelGenerators.image Subtype.val ∪ imageGenerators.image lift
  let Generated := Subgroup.closure (generators : Set Source)
  have hkernelLe : quotient.ker ≤ Generated := by
    have hmapLe : (Subgroup.closure (kernelGenerators : Set quotient.ker)).map quotient.ker.subtype ≤
        Generated := by
      rw [map_generated_subgroup]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨element, helement, rfl⟩
      apply Subgroup.subset_closure
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨element, helement, rfl⟩)
    intro element helement
    apply hmapLe
    exact Subgroup.mem_map.mpr ⟨⟨element, helement⟩, hkernel ▸ Subgroup.mem_top _, rfl⟩
  have himageTop : Generated.map quotient = ⊤ := by
    apply top_unique
    rw [← himage]
    apply (Subgroup.closure_le _).mpr
    intro element helement
    exact Subgroup.mem_map.mpr ⟨lift element,
      Subgroup.subset_closure (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨element, helement, rfl⟩)), hlift element⟩
  have hgenerated : Generated = ⊤ := by
    have hpreimage := congrArg (Subgroup.comap quotient) himageTop
    rw [Subgroup.comap_map_eq, Subgroup.comap_top, sup_eq_left.mpr hkernelLe] at hpreimage
    exact hpreimage
  refine ⟨generators, hgenerated, ?_⟩
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

theorem extension_generator_bound {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (quotient : Source →* Target)
    (hsurjective : Function.Surjective quotient) {kernelBound imageBound : ℕ}
    (hkernel : ∃ generators : Finset quotient.ker,
      Subgroup.closure (generators : Set quotient.ker) = ⊤ ∧ generators.card ≤ kernelBound)
    (himage : ∃ generators : Finset Target,
      Subgroup.closure (generators : Set Target) = ⊤ ∧ generators.card ≤ imageBound) :
    ∃ generators : Finset Source,
      Subgroup.closure (generators : Set Source) = ⊤ ∧
        generators.card ≤ kernelBound + imageBound := by
  obtain ⟨kernelGenerators, hkernelGenerates, hkernelCard⟩ := hkernel
  obtain ⟨imageGenerators, himageGenerates, himageCard⟩ := himage
  obtain ⟨generators, hgenerates, hcard⟩ := extension_generators quotient hsurjective
    kernelGenerators imageGenerators hkernelGenerates himageGenerates
  exact ⟨generators, hgenerates, hcard.trans (Nat.add_le_add hkernelCard himageCard)⟩

end CFSG.LargeEvenClassification.Helpers
