module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.NormalInducedFamilyWeightedNorm
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open scoped ComplexConjugate

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {R : G → Subgroup G}
  {H : Subgroup ↥L} {ζ : ↥L → ℂ}

section Domain

variable [Fintype ↥L]

theorem indClassFun_one_sub_mem_dadeDomain [H.Normal]
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ)) :
    indClassFun H (1 : ↥H → ℂ) - ζ ∈ dadeDomain L A := by
  refine mem_dadeDomain_of_mem_span_indFam hA (subset_refl _) ?_ ?_
  · exact sub_mem (Submodule.subset_span (indClassFun_one_mem_indFam H))
      (Submodule.subset_span (indFam_mono H Set.sdiff_subset hζS))
  · simp [NormalInducedWeightedNorm.indClassFun_one_apply_one, hζ1]

theorem indClassFun_one_sub_mem_span_Irr (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) :
    indClassFun H (1 : ↥H → ℂ) - ζ ∈ Submodule.span ℤ (Irr ↥L) := by
  obtain ⟨W, hW⟩ := exists_fdRep_character_eq_of_mem_indFam H (indClassFun_one_mem_indFam H)
  obtain ⟨V, hV⟩ := exists_fdRep_character_eq_of_mem_indFam H
    (indFam_mono H Set.sdiff_subset hζS)
  exact sub_mem (hW ▸ FDRep.character_mem_span_Irr W) (hV ▸ FDRep.character_mem_span_Irr V)

theorem cfInner_indClassFun_one_left_one :
    cfInner (indClassFun H (1 : ↥H → ℂ)) (1 : ↥L → ℂ) = 1 := by
  have : Fintype ↥H := Fintype.ofFinite _
  rw [cfInner_indClassFun H (1 : ↥H → ℂ) (one_mem_classFun ↥L), resClassFun_one, cfInner_one_one]

theorem cfInner_indClassFun_one_sub_one [H.Normal] (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) :
    cfInner (indClassFun H (1 : ↥H → ℂ) - ζ) (1 : ↥L → ℂ) = 1 := by
  rw [cfInner_sub_left, cfInner_indClassFun_one_left_one,
    cfInner_one_of_mem_indFam_sdiff hζS, sub_zero]

theorem cfInner_self_indClassFun_one_sub [H.Normal] (hζS : ζ ∈ indFam H (Irr ↥H \ {1}))
    (hζIrr : ζ ∈ Irr ↥L) :
    cfInner (indClassFun H (1 : ↥H → ℂ) - ζ) (indClassFun H (1 : ↥H → ℂ) - ζ)
      = (H.index : ℂ) + 1 := by
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hζS
  have h1 : cfInner (indClassFun H θ) (indClassFun H (1 : ↥H → ℂ)) = 0 :=
    cfInner_indClassFun_indClassFun_one H hθ hθ1
  have h2 : cfInner (indClassFun H (1 : ↥H → ℂ)) (indClassFun H θ) = 0 := by
    rw [← conj_cfInner, h1, map_zero]
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    NormalInducedWeightedNorm.cfInner_self_indClassFun_one, h1, h2,
    cfInner_self_of_mem_Irr hζIrr]
  ring

end Domain

section Beta

variable [Fintype ↥L]

noncomputable def dadeBeta (A : Set G) (R : G → Subgroup G) (H : Subgroup ↥L) (ζ : ↥L → ℂ) :
    G → ℂ :=
  dadeSupportExtension A R (extendByZero L (indClassFun H (1 : ↥H → ℂ) - ζ))

theorem dadeBeta_eq_dadeMap [Finite G] (hD : IsDadeData L A R)
    (hβ : indClassFun H (1 : ↥H → ℂ) - ζ ∈ dadeDomain L A) :
    dadeBeta A R H ζ
      = ((dadeMap hD ⟨indClassFun H (1 : ↥H → ℂ) - ζ, hβ⟩ : classFun G) : G → ℂ) := by
  rw [dadeBeta, dadeMap_apply_coe hD ⟨indClassFun H (1 : ↥H → ℂ) - ζ, hβ⟩]

theorem dadeBeta_apply_of_mem_dadeSupport [Finite G] (hD : IsDadeData L A R)
    (hβ : indClassFun H (1 : ↥H → ℂ) - ζ ∈ dadeDomain L A) {a : G} (ha : a ∈ A) {x : G}
    (hx : x ∈ dadeSupport R a) :
    dadeBeta A R H ζ x
      = indClassFun H (1 : ↥H → ℂ) ⟨a, hD.mem_of_mem ha⟩ - ζ ⟨a, hD.mem_of_mem ha⟩ := by
  rw [dadeBeta_eq_dadeMap hD hβ, dadeMap_apply_of_mem_dadeSupport hD _ ha hx]
  rfl

theorem dadeBeta_eq_zero_of_notMem [Finite G] (hD : IsDadeData L A R)
    (hβ : indClassFun H (1 : ↥H → ℂ) - ζ ∈ dadeDomain L A) {x : G}
    (hx : x ∉ totalDadeSupport A R) : dadeBeta A R H ζ x = 0 := by
  rw [dadeBeta_eq_dadeMap hD hβ]
  exact dadeMap_eq_zero_of_notMem hD _ hx

section Main

variable [Finite G] [H.Normal]
  (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ))

include hD hA hζS hζ1 in
theorem dadeBeta_eq_dadeMap_indClassFun_one_sub :
    dadeBeta A R H ζ = ((dadeMap hD
      ⟨indClassFun H (1 : ↥H → ℂ) - ζ,
        indClassFun_one_sub_mem_dadeDomain hA hζS hζ1⟩ : classFun G) : G → ℂ) :=
  dadeBeta_eq_dadeMap hD _

include hD hA hζS hζ1 in
theorem dadeBeta_mem_classFun : dadeBeta A R H ζ ∈ classFun G := by
  rw [dadeBeta_eq_dadeMap_indClassFun_one_sub hD hA hζS hζ1]
  exact (dadeMap hD _).2

include hD hA hζS hζ1 in
theorem dadeBeta_mem_virtualChars : dadeBeta A R H ζ ∈ virtualChars G := by
  rw [dadeBeta_eq_dadeMap_indClassFun_one_sub hD hA hζS hζ1]
  exact mem_virtualChars_of_mem_span_Irr
    (hD.dadeMap_mem_span_Irr _ (indClassFun_one_sub_mem_span_Irr hζS))

include hD hA hζS hζ1 in
theorem dadeBeta_apply_one : dadeBeta A R H ζ 1 = 0 := by
  rw [dadeBeta_eq_dadeMap_indClassFun_one_sub hD hA hζS hζ1]
  exact dadeMap_one_eq_zero hD _

include hD hA hζS hζ1 in
theorem cfInner_dadeBeta_one [Fintype G] : cfInner (dadeBeta A R H ζ) (1 : G → ℂ) = 1 := by
  rw [dadeBeta_eq_dadeMap_indClassFun_one_sub hD hA hζS hζ1, cfInner_dadeMap_one hD _,
    cfInner_indClassFun_one_sub_one hζS]

include hD hA hζS hζ1 in
theorem cfInner_self_dadeBeta [Fintype G] (hζIrr : ζ ∈ Irr ↥L) :
    cfInner (dadeBeta A R H ζ) (dadeBeta A R H ζ) = (H.index : ℂ) + 1 := by
  rw [dadeBeta_eq_dadeMap_indClassFun_one_sub hD hA hζS hζ1, cfInner_self_dadeMap hD _,
    cfInner_self_indClassFun_one_sub hζS hζIrr]

include hD hA hζS hζ1 in
theorem dadeBeta_spec [Fintype G] (hζIrr : ζ ∈ Irr ↥L) :
    dadeBeta A R H ζ ∈ virtualChars G ∧ dadeBeta A R H ζ 1 = 0 ∧
      cfInner (dadeBeta A R H ζ) (1 : G → ℂ) = 1 ∧
      cfInner (dadeBeta A R H ζ) (dadeBeta A R H ζ) = (H.index : ℂ) + 1 :=
  ⟨dadeBeta_mem_virtualChars hD hA hζS hζ1, dadeBeta_apply_one hD hA hζS hζ1,
    cfInner_dadeBeta_one hD hA hζS hζ1, cfInner_self_dadeBeta hD hA hζS hζ1 hζIrr⟩

end Main

end Beta

end NormalInducedFamily

end CFSG.FeitThompson
