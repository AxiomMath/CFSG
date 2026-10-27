module

public import CFSG.FeitThompson.Representations.DadeRealCorrectedCharacter
public import CFSG.FeitThompson.Representations.DisjointDadeSupportsOrthogonalIrreducibles
import CFSG.FeitThompson.Representations.ParityRealCharacterInnerProducts

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate

section Support

variable {G : Type*} [Group G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {S : Set (↥L → ℂ)} {ζ : ↥L → ℂ}

theorem support_dadeBeta_subset [Finite G] (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hS : S = indFam H (Irr ↥H \ {1})) (hζS : ζ ∈ S) (hζ1 : ζ 1 = (H.index : ℂ)) :
    Function.support (dadeBeta A R H ζ) ⊆ totalDadeSupport A R := by
  intro x hx
  by_contra hx'
  exact hx (dadeBeta_eq_zero_of_notMem hD
    (indClassFun_one_sub_mem_dadeDomain hA (hS ▸ hζS) hζ1) hx')

theorem nontrivial_of_mem_of_mem_Irr (hodd : Odd (Nat.card G))
    (hS : S = indFam H (Irr ↥H \ {1})) (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) : S.Nontrivial :=
  ⟨star ζ, star_mem_of_mem hS hζS, ζ, hζS, star_ne_self_of_odd hodd hS hζS hζIrr⟩

end Support

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
  (hζ₁S : ζ₁ ∈ S₁) (hζ₁Irr : ζ₁ ∈ Irr ↥L₁) (hζ₁1 : ζ₁ 1 = (H₁.index : ℂ))
  (hζ₂S : ζ₂ ∈ S₂) (hζ₂Irr : ζ₂ ∈ Irr ↥L₂) (hζ₂1 : ζ₂ 1 = (H₂.index : ℂ))
  (hdisj : Disjoint (totalDadeSupport A₁ R₁) (totalDadeSupport A₂ R₂))

include hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hζ₁S hζ₁1 hζ₂S hζ₂1 hdisj in
theorem cfInner_dadeBeta_dadeBeta_eq_zero :
    cfInner (dadeBeta A₁ R₁ H₁ ζ₁) (dadeBeta A₂ R₂ H₂ ζ₂) = 0 :=
  cfInner_eq_zero_of_disjoint_support
    (hdisj.mono (support_dadeBeta_subset hD₁ hA₁ hS₁ hζ₁S hζ₁1)
      (support_dadeBeta_subset hD₂ hA₂ hS₂ hζ₂S hζ₂1))

include hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ hζ₁Irr hζ₁1 hζ₂Irr hζ₂1 hdisj in
theorem cfInner_dadeDelta_dadeDelta_eq_add :
    cfInner (dadeDelta A₁ R₁ H₁ ν₁ hζ₁S) (dadeDelta A₂ R₂ H₂ ν₂ hζ₂S)
      = cfInner (dadeBeta A₁ R₁ H₁ ζ₁) (ν₂ ⟨ζ₂, Submodule.subset_span hζ₂S⟩ : G → ℂ)
        + conj (cfInner (dadeBeta A₂ R₂ H₂ ζ₂)
            (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ)) := by
  rw [dadeDelta_eq, dadeDelta_eq, cfInner_add_left, cfInner_add_right, cfInner_add_right,
    cfInner_dadeBeta_dadeBeta_eq_zero hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hζ₁S hζ₁1 hζ₂S hζ₂1 hdisj,
    cfInner_nu_nu_eq_zero_of_disjoint_totalDadeSupport hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso
      hν₁τ hν₂τ hζ₁S hζ₁Irr hζ₂S hζ₂Irr hdisj,
    ← conj_cfInner (dadeBeta A₂ R₂ H₂ ζ₂) (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ)]
  ring

omit hdisj in
include hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ hζ₁Irr hζ₁1 hζ₂Irr hζ₂1 in
theorem cfInner_dadeDelta_dadeDelta_ne_zero :
    cfInner (dadeDelta A₁ R₁ H₁ ν₁ hζ₁S) (dadeDelta A₂ R₂ H₂ ν₂ hζ₂S) ≠ 0 := by
  have h1 : cfInner (dadeDelta A₁ R₁ H₁ ν₁ hζ₁S) (1 : G → ℂ) = 1 :=
    cfInner_dadeDelta_one hD₁ hA₁ hS₁ hν₁iso hν₁τ hζ₁S hζ₁Irr hζ₁1
      (nontrivial_of_mem_of_mem_Irr hodd hS₁ hζ₁S hζ₁Irr)
  have h2 : cfInner (dadeDelta A₂ R₂ H₂ ν₂ hζ₂S) (1 : G → ℂ) = 1 :=
    cfInner_dadeDelta_one hD₂ hA₂ hS₂ hν₂iso hν₂τ hζ₂S hζ₂Irr hζ₂1
      (nontrivial_of_mem_of_mem_Irr hodd hS₂ hζ₂S hζ₂Irr)
  obtain ⟨k, hk⟩ := exists_int_cfInner_sub_mul_cfInner_one_eq_two_mul_of_odd hodd
    (mem_span_Irr_of_mem_virtualChars (dadeDelta_mem_virtualChars hD₁ hA₁ hS₁ hζ₁S hζ₁1))
    (mem_span_Irr_of_mem_virtualChars (dadeDelta_mem_virtualChars hD₂ hA₂ hS₂ hζ₂S hζ₂1))
    (dadeDelta_apply_im hodd hD₁ hA₁ hS₁ hν₁iso hν₁τ hζ₁S hζ₁Irr hζ₁1)
    (dadeDelta_apply_im hodd hD₂ hA₂ hS₂ hν₂iso hν₂τ hζ₂S hζ₂Irr hζ₂1)
  rw [h1, h2, mul_one] at hk
  have hval : cfInner (dadeDelta A₁ R₁ H₁ ν₁ hζ₁S) (dadeDelta A₂ R₂ H₂ ν₂ hζ₂S)
      = ((2 * k + 1 : ℤ) : ℂ) := by push_cast; linear_combination hk
  rw [hval]
  simp only [ne_eq, Int.cast_eq_zero]
  omega

include hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ hζ₁Irr hζ₁1 hζ₂Irr hζ₂1 hdisj in
theorem cfInner_dadeBeta_nu_ne_zero_or_swap :
    cfInner (dadeBeta A₁ R₁ H₁ ζ₁) (ν₂ ⟨ζ₂, Submodule.subset_span hζ₂S⟩ : G → ℂ) ≠ 0 ∨
      cfInner (dadeBeta A₂ R₂ H₂ ζ₂) (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ) ≠ 0 := by
  by_contra hcon
  rw [not_or, not_ne_iff, not_ne_iff] at hcon
  refine cfInner_dadeDelta_dadeDelta_ne_zero hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ
    hζ₁S hζ₁Irr hζ₁1 hζ₂S hζ₂Irr hζ₂1 ?_
  rw [cfInner_dadeDelta_dadeDelta_eq_add hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ
    hζ₁S hζ₁Irr hζ₁1 hζ₂S hζ₂Irr hζ₂1 hdisj, hcon.1, hcon.2]
  simp

include hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ hν₂τ hζ₁Irr hζ₁1 hζ₂Irr hζ₂1 hdisj in
theorem not_isOrthogonal_dadeBeta_nu_or_swap :
    ¬ IsOrthogonal (dadeBeta A₁ R₁ H₁ ζ₁) (ν₂ ⟨ζ₂, Submodule.subset_span hζ₂S⟩ : G → ℂ) ∨
      ¬ IsOrthogonal (dadeBeta A₂ R₂ H₂ ζ₂) (ν₁ ⟨ζ₁, Submodule.subset_span hζ₁S⟩ : G → ℂ) := by
  have h := cfInner_dadeBeta_nu_ne_zero_or_swap hodd hD₁ hD₂ hA₁ hA₂ hS₁ hS₂ hν₁iso hν₂iso hν₁τ
    hν₂τ hζ₁S hζ₁Irr hζ₁1 hζ₂S hζ₂Irr hζ₂1 hdisj
  rcases h with h | h
  · exact Or.inl fun hc => h (isOrthogonal_iff.1 hc)
  · exact Or.inr fun hc => h (isOrthogonal_iff.1 hc)

end Main

end NormalInducedFamily

end CFSG.FeitThompson

end
