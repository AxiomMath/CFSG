module

public import CFSG.FeitThompson.Representations.CoreCoherentIrreducibleArrayOrthogonality
import CFSG.FeitThompson.Representations.PrincipalColumnProjectionNormalizedPivot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PartialCoherent

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K : Subgroup ↥L} [K.Normal] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {A0 : Set G} {T : G → Subgroup G} {ω : classFun ↥W →ₗ[ℂ] classFun G}
  {P : Set (↥L → ℂ)} {τ : charSpanZero P →+ virtualChars G}
  {ν : Submodule.span ℤ P →+ virtualChars G} {ζ : ↥L → ℂ}
  (hodd : Odd (Nat.card G))
  (hW : IsCyclicTIPair W W1 W2)
  (hW2K : W2 ≤ K.map L.subtype)
  (hW1K : W1 ⊓ K.map L.subtype = ⊥)
  (hω : IsCyclicTIIsometry W W1 W2 ω)
  (hD : IsDadeData L A0 T)
  (hKA : (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A0)
  (hVA : cyclicTIDiff W W1 W2 ⊆ A0)
  (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
  (hPstar : ∀ χ ∈ P, star χ ∈ P)
  (hν : IsCoherentWith P τ ν)
  (hτ : ∀ (f : charSpanZero P) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
    (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζP : ζ ∈ P) (hζIrr : ζ ∈ Irr ↥L)

omit [Fintype G] [Fintype ↥W] [K.Normal] in
include hPS in
theorem subset_indFamDetect_top : P ⊆ indFamDetect K (⊤ : Subgroup ↥K) := fun _ hx =>
  PrimeDadePivot.indFam_sdiff_subset_indFamDetect_top K (hPS hx)

omit [Fintype G] [Fintype ↥W] in
include hKA hPS in
theorem apply_eq_zero_of_notMem (f : charSpanZero P) (x : ↥L) (hx : (x : G) ∉ A0) :
    (f : ↥L → ℂ) x = 0 := by
  by_cases hxK : x ∈ K
  · by_cases hx1 : x = 1
    · rw [hx1]; exact charSpanZero_apply_one f
    · exact absurd (hKA ⟨x, ⟨hxK, by simpa using hx1⟩, rfl⟩) hx
  · exact apply_eq_zero_of_mem_span_indFamDetect (subset_indFamDetect_top hPS)
      (charSpanZero_le _ f.2) hxK

omit [Fintype ↥W] in
include hD hν hτ in
theorem coe_nu_eq_dadeMap (f : Submodule.span ℤ P) (F : dadeDomain L A0)
    (h : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have h1 : ((1 : ↥L) : G) ∉ A0 := by simpa using hD.one_notMem
  have hone : (f : ↥L → ℂ) 1 = 0 := by
    rw [h]; exact dadeDomain.apply_eq_zero F.2 h1
  have hz : (f : ↥L → ℂ) ∈ charSpanZero P := mem_charSpanZero.2 ⟨f.2, hone⟩
  have key := hν.eq_on_zero ⟨(f : ↥L → ℂ), hz⟩
  have hincl : Submodule.inclusion (charSpanZero_le P) ⟨(f : ↥L → ℂ), hz⟩ = f := Subtype.ext rfl
  rw [hincl] at key
  rw [key]
  exact hτ ⟨(f : ↥L → ℂ), hz⟩ F h

omit [Fintype ↥W] in
include hν hζIrr in
theorem cfInner_self_nu_eq_one :
    cfInner (ν ⟨ζ, Submodule.subset_span hζP⟩ : G → ℂ)
      (ν ⟨ζ, Submodule.subset_span hζP⟩ : G → ℂ) = 1 := by
  rw [hν.inner_eq]
  exact cfInner_self_of_mem_Irr hζIrr

include hodd hW hW2K hW1K hω hD hKA hVA hPS hPstar hν hτ hζIrr in
theorem cfInner_nu_apply_eq_zero {χ : classFun ↥W} (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) :
    cfInner (ν ⟨ζ, Submodule.subset_span hζP⟩ : G → ℂ) (ω χ : G → ℂ) = 0 := by
  refine cfInner_apply_eq_zero_of_forall_prodCharEta hW (fun i j => ?_) χ
  exact isOrthogonal_iff.1 (CoherentCore.isOrthogonal_nu_prodCharEta hodd hW hW2K hW1K hω hD hVA
    (subset_indFamDetect_top hPS) hPstar hν.inner_eq (apply_eq_zero_of_notMem hKA hPS)
    (coe_nu_eq_dadeMap hD hν hτ) hζP hζIrr i j)

include hodd hW hW2K hW1K hω hD hKA hVA hPS hPstar hν hτ hζIrr in
theorem cfInner_nu_prodCharEta_eq_zero (i : Irr ↥W1) (j : Irr ↥W2) :
    cfInner (ν ⟨ζ, Submodule.subset_span hζP⟩ : G → ℂ) (hW.prodCharEta ω i j) = 0 :=
  isOrthogonal_iff.1 (CoherentCore.isOrthogonal_nu_prodCharEta hodd hW hW2K hW1K hω hD hVA
    (subset_indFamDetect_top hPS) hPstar hν.inner_eq (apply_eq_zero_of_notMem hKA hPS)
    (coe_nu_eq_dadeMap hD hν hτ) hζP hζIrr i j)

include hodd hW hW2K hW1K hω hD hKA hVA hPS hPstar hν hτ hζIrr in
theorem nu_apply_eq_zero_of_mem_cyclicTIDiff {v : G} (hv : v ∈ cyclicTIDiff W W1 W2) :
    (ν ⟨ζ, Submodule.subset_span hζP⟩ : G → ℂ) v = 0 :=
  CoherentCore.nu_apply_eq_zero_of_mem_cyclicTIDiff hodd hW hW2K hW1K hω hD hVA
    (subset_indFamDetect_top hPS) hPstar hν.inner_eq (apply_eq_zero_of_notMem hKA hPS)
    (coe_nu_eq_dadeMap hD hν hτ) hζP hζIrr hv

end PartialCoherent

end CFSG.FeitThompson

end
