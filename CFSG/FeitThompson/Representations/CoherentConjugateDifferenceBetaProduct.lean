module

public import CFSG.FeitThompson.Representations.DadeBetaIntegralDegreeZero
public import CFSG.FeitThompson.Representations.CoherentNormalIrreducibleConjugation
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.DegreeZeroIsometryDisjointConjPairs
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {R : G → Subgroup G}
  {H : Subgroup ↥L} {ζ : ↥L → ℂ} {S : Set (↥L → ℂ)}

section Source

variable [Fintype ↥L] [H.Normal]
  (hodd : Odd (Nat.card G)) (hS : S = indFam H (Irr ↥H \ {1}))
  (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) (hζ1 : ζ 1 = (H.index : ℂ))

theorem cfInner_indClassFun_one_eq_zero_of_mem_indFam_sdiff {ξ : ↥L → ℂ}
    (hξ : ξ ∈ indFam H (Irr ↥H \ {1})) :
    cfInner ξ (indClassFun H (1 : ↥H → ℂ)) = 0 :=
  cfInner_indClassFun_one_of_mem_indFam_diff H (by rw [indFam_diff_singleton]; exact hξ)

include hodd hS hζS hζIrr in
theorem cfInner_sub_star_indClassFun_one_sub :
    cfInner (ζ - star ζ) (indClassFun H (1 : ↥H → ℂ) - ζ) = -1 := by
  have hζS' : ζ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ hζS
  have hstarS' : star ζ ∈ indFam H (Irr ↥H \ {1}) := star_mem_indFam_sdiff hζS'
  have hne : star ζ ≠ ζ := star_ne_self_of_odd hodd hS hζS hζIrr
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_indClassFun_one_eq_zero_of_mem_indFam_sdiff hζS',
    cfInner_indClassFun_one_eq_zero_of_mem_indFam_sdiff hstarS',
    cfInner_self_of_mem_Irr hζIrr,
    cfInner_eq_zero_of_mem_Irr (star_mem_Irr hζIrr) hζIrr hne]
  ring

omit [Fintype ↥L] [H.Normal] in
include hζ1 in
theorem sub_star_apply_one_eq_zero : (ζ - star ζ) 1 = 0 := by
  simp [hζ1]

include hS hζS hζ1 in
theorem sub_star_mem_dadeDomain
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) :
    ζ - star ζ ∈ dadeDomain L A := by
  refine mem_dadeDomain_of_mem_span_indFam hA (hS ▸ indFam_mono H Set.sdiff_subset) ?_
    (sub_star_apply_one_eq_zero hζ1)
  exact sub_mem (Submodule.subset_span hζS) (Submodule.subset_span (star_mem_of_mem hS hζS))

end Source

section Coherent

variable [Finite G] [Fintype ↥L] [H.Normal] {ν : Submodule.span ℤ S →+ virtualChars G}
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : S = indFam H (Irr ↥H \ {1}))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζS : ζ ∈ S) (hζ1 : ζ 1 = (H.index : ℂ))

include hD hA hS hντ hζS hζ1 in
theorem coe_nu_sub_nu_star_eq_dadeMap :
    (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ)
      = ((dadeMap hD ⟨ζ - star ζ, sub_star_mem_dadeDomain hS hζS hζ1 hA⟩ : classFun G) :
          G → ℂ) := by
  have h := hντ (⟨ζ, Submodule.subset_span hζS⟩
      - ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩)
    ⟨ζ - star ζ, sub_star_mem_dadeDomain hS hζS hζ1 hA⟩ rfl
  rw [map_sub] at h
  exact h

end Coherent

section Main

variable [Fintype G] [Fintype ↥L] [H.Normal] {ν : Submodule.span ℤ S →+ virtualChars G}
  (hodd : Odd (Nat.card G))
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : S = indFam H (Irr ↥H \ {1}))
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) (hζ1 : ζ 1 = (H.index : ℂ))

include hodd hD hA hS hνiso hντ hζS hζIrr in
theorem nu_star_mem_signedIrr :
    (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ) ∈ signedIrr G :=
  nu_mem_signedIrr hodd hD hA hS hνiso hντ (star_mem_of_mem hS hζS) (star_mem_Irr hζIrr)

include hodd hS hνiso hζS hζIrr in
theorem isOrthogonal_nu_nu_star :
    IsOrthogonal (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
      (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ) := by
  rw [isOrthogonal_iff, hνiso]
  exact cfInner_eq_zero_of_mem_Irr hζIrr (star_mem_Irr hζIrr)
    (fun h => star_ne_self_of_odd hodd hS hζS hζIrr h.symm)

omit hνiso in
include hodd hD hA hS hντ hζS hζIrr hζ1 in
theorem cfInner_nu_sub_nu_star_dadeBeta :
    cfInner ((ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ))
      (dadeBeta A R H ζ) = -1 := by
  have hζS' : ζ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ hζS
  rw [coe_nu_sub_nu_star_eq_dadeMap hD hA hS hντ hζS hζ1,
    dadeBeta_eq_dadeMap_indClassFun_one_sub hD hA hζS' hζ1, cfInner_dadeMap hD]
  exact cfInner_sub_star_indClassFun_one_sub hodd hS hζS hζIrr

include hodd hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem nu_conjugate_difference_spec :
    star ζ ∈ S ∧
      (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) ∈ signedIrr G ∧
      (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ) ∈ signedIrr G ∧
      IsOrthogonal (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ) ∧
      (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
          - (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ)
        = ((dadeMap hD ⟨ζ - star ζ, sub_star_mem_dadeDomain hS hζS hζ1 hA⟩ : classFun G) :
            G → ℂ) ∧
      cfInner ((ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
          - (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ))
        (dadeBeta A R H ζ) = -1 :=
  ⟨star_mem_of_mem hS hζS, nu_mem_signedIrr hodd hD hA hS hνiso hντ hζS hζIrr,
    nu_star_mem_signedIrr hodd hD hA hS hνiso hντ hζS hζIrr,
    isOrthogonal_nu_nu_star hodd hS hνiso hζS hζIrr,
    coe_nu_sub_nu_star_eq_dadeMap hD hA hS hντ hζS hζ1,
    cfInner_nu_sub_nu_star_dadeBeta hodd hD hA hS hντ hζS hζIrr hζ1⟩

end Main

end NormalInducedFamily

end CFSG.FeitThompson

end
