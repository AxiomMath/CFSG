module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.CoherentNormalIrreducibleConjugation
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

section Family

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {S : Set (↥L → ℂ)} {ζ : ↥L → ℂ}
  {ν : Submodule.span ℤ S →+ virtualChars G}
  (hodd : Odd (Nat.card G))
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : S = indFam H (Irr ↥H \ {1}))
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))

omit [Fintype G] in
include hA hS in
theorem sub_star_mem_dadeDomain_of_mem_Irr (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    ζ - star ζ ∈ dadeDomain L A := by
  refine mem_dadeDomain_of_mem_span_indFam hA (by rw [hS]; exact indFam_mono H Set.sdiff_subset)
    (sub_mem (Submodule.subset_span hζS)
      (Submodule.subset_span (star_mem_of_mem hS hζS))) ?_
  simp [conj_apply_one_of_mem_Irr hζIrr]

include hodd hD hA hS hνiso hντ in
theorem coe_nu_sub_star_eq_dadeMap (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
      = ((dadeMap hD ⟨ζ - star ζ, sub_star_mem_dadeDomain_of_mem_Irr hA hS hζS hζIrr⟩ :
          classFun G) : G → ℂ) := by
  have hsub : ζ - star ζ ∈ Submodule.span ℤ S :=
    sub_mem (Submodule.subset_span hζS) (Submodule.subset_span (star_mem_of_mem hS hζS))
  have key : (ν ⟨ζ - star ζ, hsub⟩ : G → ℂ)
      = (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - (ν ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ : G → ℂ) := by
    rw [show (⟨ζ - star ζ, hsub⟩ : Submodule.span ℤ S)
        = ⟨ζ, Submodule.subset_span hζS⟩
          - ⟨star ζ, Submodule.subset_span (star_mem_of_mem hS hζS)⟩ from rfl, map_sub]
    rfl
  rw [← coe_nu_star_eq hodd hD hA hS hνiso hντ hζS hζIrr, ← key]
  exact hντ _ _ rfl

include hodd hD hA hS hνiso hντ in
theorem support_coe_nu_sub_star_subset (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) :
    Function.support ((ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ))
      ⊆ totalDadeSupport A R := by
  rw [coe_nu_sub_star_eq_dadeMap hodd hD hA hS hνiso hντ hζS hζIrr]
  exact support_dadeMap_subset hD _

end Family

section Main

variable {G : Type*} [Group G] [Fintype G] {L₁ L₂ : Subgroup G} [Fintype ↥L₁] [Fintype ↥L₂]
  {A₁ A₂ : Set G} {R₁ R₂ : G → Subgroup G} {H₁ : Subgroup ↥L₁} [H₁.Normal] {H₂ : Subgroup ↥L₂}
  [H₂.Normal] {S₁ : Set (↥L₁ → ℂ)} {S₂ : Set (↥L₂ → ℂ)}
  {ν₁ : Submodule.span ℤ S₁ →+ virtualChars G} {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G}
  {ζ₁ : ↥L₁ → ℂ} {ζ₂ : ↥L₂ → ℂ}
  (hodd : Odd (Nat.card G))
  (hD₁ : IsDadeData L₁ A₁ R₁) (hD₂ : IsDadeData L₂ A₂ R₂)
  (hA₁ : A₁ = (fun x : ↥L₁ => (x : G)) '' ((H₁ : Set ↥L₁) \ {1}))
  (hA₂ : A₂ = (fun x : ↥L₂ => (x : G)) '' ((H₂ : Set ↥L₂) \ {1}))
  (hS₁ : S₁ = indFam H₁ (Irr ↥H₁ \ {1})) (hS₂ : S₂ = indFam H₂ (Irr ↥H₂ \ {1}))
  (hν₁iso : ∀ f h : Submodule.span ℤ S₁,
    cfInner (ν₁ f : G → ℂ) (ν₁ h : G → ℂ) = cfInner (f : ↥L₁ → ℂ) (h : ↥L₁ → ℂ))
  (hν₂iso : ∀ f h : Submodule.span ℤ S₂,
    cfInner (ν₂ f : G → ℂ) (ν₂ h : G → ℂ) = cfInner (f : ↥L₂ → ℂ) (h : ↥L₂ → ℂ))
  (hν₁τ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L₁ A₁), (f : ↥L₁ → ℂ) = (F : ↥L₁ → ℂ) →
    (ν₁ f : G → ℂ) = ((dadeMap hD₁ F : classFun G) : G → ℂ))
  (hν₂τ : ∀ (f : Submodule.span ℤ S₂) (F : dadeDomain L₂ A₂), (f : ↥L₂ → ℂ) = (F : ↥L₂ → ℂ) →
    (ν₂ f : G → ℂ) = ((dadeMap hD₂ F : classFun G) : G → ℂ))
  (hζ₁S : ζ₁ ∈ S₁) (hζ₁Irr : ζ₁ ∈ Irr ↥L₁) (hζ₂S : ζ₂ ∈ S₂) (hζ₂Irr : ζ₂ ∈ Irr ↥L₂)
  (hdisj : Disjoint (totalDadeSupport A₁ R₁) (totalDadeSupport A₂ R₂))

include hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ hζ₁Irr hζ₂Irr hdisj in
theorem cfInner_nu_nu_eq_zero_of_disjoint_totalDadeSupport :
    cfInner (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ)
      (ν₂ ⟨ζ₂, Submodule.subset_span hζ₂S⟩ : G → ℂ) = 0 := by
  obtain ⟨ε₁, hε₁, χ₁, hχ₁, hχ₁nr, hval₁⟩ :=
    exists_sign_nonreal_Irr_nu hodd hD₁ hA₁ hS₁ hν₁iso hν₁τ hζ₁S hζ₁Irr
  obtain ⟨ε₂, hε₂, χ₂, hχ₂, -, hval₂⟩ :=
    exists_sign_nonreal_Irr_nu hodd hD₂ hA₂ hS₂ hν₂iso hν₂τ hζ₂S hζ₂Irr
  have hstarε₁ : star ε₁ = ε₁ := by rcases hε₁ with rfl | rfl <;> simp
  have hstarε₂ : star ε₂ = ε₂ := by rcases hε₂ with rfl | rfl <;> simp
  have hε₁ne : ε₁ ≠ 0 := by rcases hε₁ with rfl | rfl <;> simp
  have hε₂ne : (starRingEnd ℂ) ε₂ ≠ 0 := by rcases hε₂ with rfl | rfl <;> simp
  have hd₁ : (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ)
      - star (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ) = ε₁ • (χ₁ - star χ₁) := by
    rw [hval₁, star_smul, hstarε₁, smul_sub]
  have hd₂ : (ν₂ ⟨ζ₂, Submodule.subset_span hζ₂S⟩ : G → ℂ)
      - star (ν₂ ⟨ζ₂, Submodule.subset_span hζ₂S⟩ : G → ℂ) = ε₂ • (χ₂ - star χ₂) := by
    rw [hval₂, star_smul, hstarε₂, smul_sub]
  have hzero : cfInner (ε₁ • (χ₁ - star χ₁)) (ε₂ • (χ₂ - star χ₂)) = 0 := by
    rw [← hd₁, ← hd₂]
    exact cfInner_eq_zero_of_disjoint_support
      (hdisj.mono (support_coe_nu_sub_star_subset hodd hD₁ hA₁ hS₁ hν₁iso hν₁τ hζ₁S hζ₁Irr)
        (support_coe_nu_sub_star_subset hodd hD₂ hA₂ hS₂ hν₂iso hν₂τ hζ₂S hζ₂Irr))
  rw [cfInner_smul_left, cfInner_smul_right] at hzero
  have hpair : cfInner (χ₁ - star χ₁) (χ₂ - star χ₂) = 0 := by
    simpa [hε₁ne, hε₂ne] using hzero
  rw [hval₁, hval₂, cfInner_smul_left, cfInner_smul_right,
    DisjointCoherentFamilies.cfInner_eq_zero_of_cfInner_sub_star_eq_zero hχ₁ hχ₂ hχ₁nr hpair]
  ring

include hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ hζ₁Irr hζ₂Irr hdisj in
theorem isOrthogonal_nu_nu_of_disjoint_totalDadeSupport :
    IsOrthogonal (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ)
      (ν₂ ⟨ζ₂, Submodule.subset_span hζ₂S⟩ : G → ℂ) :=
  isOrthogonal_iff.2 (cfInner_nu_nu_eq_zero_of_disjoint_totalDadeSupport hodd hD₁ hD₂ hA₁ hA₂
    hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ hζ₁S hζ₁Irr hζ₂S hζ₂Irr hdisj)

end Main

end NormalInducedFamily

end CFSG.FeitThompson

end
