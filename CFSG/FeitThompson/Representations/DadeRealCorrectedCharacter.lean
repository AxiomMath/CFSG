module

public import CFSG.FeitThompson.Representations.CoherentConjugateDifferenceBetaProduct
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate

variable {G : Type*} [Group G] {L : Subgroup G} [Fintype ↥L] {A : Set G} {R : G → Subgroup G}
  {H : Subgroup ↥L} {S : Set (↥L → ℂ)} {ζ : ↥L → ℂ}

noncomputable def dadeDelta (A : Set G) (R : G → Subgroup G) (H : Subgroup ↥L)
    {S : Set (↥L → ℂ)} (ν : Submodule.span ℤ S →+ virtualChars G) {ζ : ↥L → ℂ} (hζS : ζ ∈ S) :
    G → ℂ :=
  dadeBeta A R H ζ + (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)

theorem dadeDelta_eq (ν : Submodule.span ℤ S →+ virtualChars G) (hζS : ζ ∈ S) :
    dadeDelta A R H ν hζS
      = dadeBeta A R H ζ + (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) := (rfl)

theorem dadeDelta_apply (ν : Submodule.span ℤ S →+ virtualChars G) (hζS : ζ ∈ S) (x : G) :
    dadeDelta A R H ν hζS x
      = dadeBeta A R H ζ x + (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) x := (rfl)

theorem star_indClassFun_one (H : Subgroup ↥L) :
    star (indClassFun H (1 : ↥H → ℂ)) = indClassFun H (1 : ↥H → ℂ) := by
  rw [← DisjointCoherentFamilies.indClassFun_star H (1 : ↥H → ℂ), star_one]

private def spanIrrHom (ν : Submodule.span ℤ S →+ virtualChars G) :
    Submodule.span ℤ S →+ Submodule.span ℤ (Irr G) where
  toFun f := ⟨(ν f : G → ℂ), mem_span_Irr_of_mem_virtualChars (ν f).2⟩
  map_zero' := by simp
  map_add' f g := by ext; simp

omit [Fintype ↥L] in
private theorem coe_spanIrrHom (ν : Submodule.span ℤ S →+ virtualChars G)
    (f : Submodule.span ℤ S) : (spanIrrHom ν f : G → ℂ) = (ν f : G → ℂ) := (rfl)

section Aux

variable [Finite G] [H.Normal] {ν : Submodule.span ℤ S →+ virtualChars G}
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : S = indFam H (Irr ↥H \ {1}))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζS : ζ ∈ S) (hζ1 : ζ 1 = (H.index : ℂ))

include hD hA hS hζS hζ1 in
theorem star_dadeBeta :
    star (dadeBeta A R H ζ)
      = dadeBeta A R H ζ
        + ((dadeMap hD ⟨ζ - star ζ, sub_star_mem_dadeDomain hS hζS hζ1 hA⟩ : classFun G)
            : G → ℂ) := by
  have hζS' : ζ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ hζS
  have hβ : indClassFun H (1 : ↥H → ℂ) - ζ ∈ dadeDomain L A :=
    indClassFun_one_sub_mem_dadeDomain hA hζS' hζ1
  have hsplit : (⟨star (indClassFun H (1 : ↥H → ℂ) - ζ), star_mem_dadeDomain hβ⟩ :
        dadeDomain L A)
      = ⟨indClassFun H (1 : ↥H → ℂ) - ζ, hβ⟩
        + ⟨ζ - star ζ, sub_star_mem_dadeDomain hS hζS hζ1 hA⟩ := by
    refine Subtype.ext ?_
    change star (indClassFun H (1 : ↥H → ℂ) - ζ)
      = (indClassFun H (1 : ↥H → ℂ) - ζ) + (ζ - star ζ)
    rw [star_sub, star_indClassFun_one]
    abel
  rw [dadeBeta_eq_dadeMap hD hβ, ← dadeMap_star hD hβ, hsplit, map_add]
  rfl

include hD hA hS hζS hζ1 in
theorem dadeDelta_mem_virtualChars : dadeDelta A R H ν hζS ∈ virtualChars G := by
  rw [dadeDelta_eq]
  exact add_mem (dadeBeta_mem_virtualChars hD hA (hS ▸ hζS) hζ1) (ν _).2

end Aux

section Main

variable [Fintype G] [H.Normal] {ν : Submodule.span ℤ S →+ virtualChars G}
  (hodd : Odd (Nat.card G))
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : S = indFam H (Irr ↥H \ {1}))
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L) (hζ1 : ζ 1 = (H.index : ℂ))

include hodd hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem star_dadeDelta : star (dadeDelta A R H ν hζS) = dadeDelta A R H ν hζS := by
  have hkey := coe_nu_sub_nu_star_eq_dadeMap hD hA hS hντ hζS hζ1
  rw [coe_nu_star_eq hodd hD hA hS hνiso hντ hζS hζIrr] at hkey
  have hβ := star_dadeBeta hD hA hS hζS hζ1 (R := R)
  rw [← hkey] at hβ
  rw [dadeDelta_eq, star_add, hβ]
  abel

include hodd hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem dadeDelta_apply_conj (x : G) :
    conj (dadeDelta A R H ν hζS x) = dadeDelta A R H ν hζS x :=
  congrFun (star_dadeDelta hodd hD hA hS hνiso hντ hζS hζIrr hζ1) x

include hodd hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem dadeDelta_apply_im (x : G) : (dadeDelta A R H ν hζS x).im = 0 :=
  Complex.conj_eq_iff_im.1 (dadeDelta_apply_conj hodd hD hA hS hνiso hντ hζS hζIrr hζ1 x)

include hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem cfInner_dadeDelta_one (hS2 : S.Nontrivial) :
    cfInner (dadeDelta A R H ν hζS) (1 : G → ℂ) = 1 := by
  have h0 : cfInner (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) (1 : G → ℂ) = 0 := by
    have h := cfInner_one_eq_zero_of_eq (ν := spanIrrHom ν) hD hA hS
      (fun f g => by rw [coe_spanIrrHom, coe_spanIrrHom]; exact hνiso f g)
      (fun f F hf => by rw [coe_spanIrrHom]; exact hντ f F hf) hζS hζIrr hζ1 hS2
    rwa [coe_spanIrrHom] at h
  rw [dadeDelta_eq, cfInner_add_left, h0, add_zero,
    cfInner_dadeBeta_one hD hA (hS ▸ hζS) hζ1]

include hodd hD hA hS hνiso hντ hζS hζIrr hζ1 in
theorem dadeDelta_spec (hS2 : S.Nontrivial) :
    dadeDelta A R H ν hζS ∈ virtualChars G ∧
      star (dadeDelta A R H ν hζS) = dadeDelta A R H ν hζS ∧
      cfInner (dadeDelta A R H ν hζS) (1 : G → ℂ) = 1 :=
  ⟨dadeDelta_mem_virtualChars hD hA hS hζS hζ1,
    star_dadeDelta hodd hD hA hS hνiso hντ hζS hζIrr hζ1,
    cfInner_dadeDelta_one hD hA hS hνiso hντ hζS hζIrr hζ1 hS2⟩

end Main

end NormalInducedFamily

end CFSG.FeitThompson

end
