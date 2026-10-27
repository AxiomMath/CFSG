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
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

theorem span_eq_top_of_irreducible [IsAlgClosed K] [FiniteDimensional K W] [Nontrivial W]
    (G : Submonoid (Module.End K W))
    (hirr : ∀ W₁ : Submodule K W, (∀ g ∈ G, ∀ w ∈ W₁, g w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤) :
    Submodule.span K (G : Set (Module.End K W)) = ⊤ := by
  classical
  set E := Algebra.adjoin K (G : Set (Module.End K W)) with hEdef
  have hsimple : IsSimpleModule E W := by
    have : Nontrivial (Submodule E W) := (Submodule.nontrivial_iff E).2 inferInstance
    refine { eq_bot_or_eq_top := fun N => ?_ }
    have hN : ∀ g ∈ G, ∀ w ∈ N.restrictScalars K, g w ∈ N.restrictScalars K := by
      intro g hg w hw
      have hgE : g ∈ E := Algebra.subset_adjoin hg
      exact N.smul_mem (⟨g, hgE⟩ : E) hw
    rcases hirr (N.restrictScalars K) hN with h | h
    · left
      exact (Submodule.restrictScalars_eq_bot_iff K E W).1 h
    · right
      exact (Submodule.restrictScalars_eq_top_iff K E W).1 h
  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := E) (V := W) K
  have hall : ∀ f : Module.End K W, f ∈ E := by
    intro f
    let F : Module.End (Module.End E W) W :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun ψ w => by
          obtain ⟨k, rfl⟩ := hschur.2 ψ
          change f ((algebraMap K (Module.End E W) k) w) = (algebraMap K (Module.End E W) k) (f w)
          simp [Module.algebraMap_end_apply] }
    set b := Module.finBasis K W
    obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
    have hfr : f = (r : Module.End K W) := b.ext fun i => by
      have := hr (b i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
      exact this
    rw [hfr]
    exact r.2
  have htop : E = ⊤ := eq_top_iff.2 fun f _ => hall f
  have hspan := Algebra.adjoin_eq_span K (G : Set (Module.End K W))
  rw [← hEdef, htop, Submonoid.closure_eq] at hspan
  rw [← hspan, Algebra.top_toSubmodule]

end CFSG.GroupTheory.HallHigmanB
