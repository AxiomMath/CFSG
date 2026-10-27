module

public import CFSG.FeitThompson.Representations.DadeBetaIntegralDegreeZero
public import CFSG.FeitThompson.Representations.NormalInducedFamilyWeightedNorm
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate
open CrossFamilyProjection (coherentImage coherentImage_apply)
open NormalInducedWeightedNorm (weightedCoherentSum weightedCoherentSum_apply)

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {ι : Type*} [Fintype ι] {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

omit [Fintype G] in
theorem cfInner_indClassFun_one_left_of_mem_indFam_sdiff {f : ↥L → ℂ}
    (hf : f ∈ indFam H (Irr ↥H \ {1})) : cfInner (indClassFun H (1 : ↥H → ℂ)) f = 0 := by
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam H).1 hf
  rw [← conj_cfInner, cfInner_indClassFun_indClassFun_one H hθ hθ1, map_zero]

omit [Fintype G] [Fintype ι] in
open scoped Classical in
theorem cfInner_indClassFun_one_sub_of_mem_range (hinj : Function.Injective ξ)
    (hS : Set.range ξ = indFam H (Irr ↥H \ {1})) (hζIrr : ξ k₀ ∈ Irr ↥L) (l : ι) :
    cfInner (indClassFun H (1 : ↥H → ℂ) - ξ k₀) (ξ l) = -(if k₀ = l then 1 else 0) := by
  have hSsub : Set.range ξ ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset
  have h1 : cfInner (indClassFun H (1 : ↥H → ℂ)) (ξ l) = 0 :=
    cfInner_indClassFun_one_left_of_mem_indFam_sdiff (hS ▸ Set.mem_range_self l)
  have h2 : cfInner (ξ k₀) (ξ l) = if k₀ = l then 1 else 0 := by
    by_cases hkl : k₀ = l
    · rw [if_pos hkl, hkl]; exact cfInner_self_of_mem_Irr (hkl ▸ hζIrr)
    · rw [if_neg hkl]
      exact cfInner_eq_zero_of_mem_indFam H (hSsub ⟨k₀, rfl⟩) (hSsub ⟨l, rfl⟩)
        fun h => hkl (hinj h)
  rw [cfInner_sub_left, h1, h2, zero_sub]

omit [Fintype G] [Fintype ↥L] [Fintype ι] in
theorem coherentImage_mem_span_Irr (l : ι) :
    coherentImage ξ ν l ∈ Submodule.span ℤ (Irr G) := by
  rw [coherentImage_apply]; exact coe_mem_span_Irr _

noncomputable def coherentHomSpan (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) :
    Submodule.span ℤ (Set.range ξ) →+ Submodule.span ℤ (Irr G) :=
  (Submodule.inclusion (virtualChars_le_span_Irr (G := G))).toAddMonoidHom.comp ν

omit [Fintype G] [Fintype ↥L] [Fintype ι] in
theorem coherentHomSpan_coe (f : Submodule.span ℤ (Set.range ξ)) :
    ((coherentHomSpan ν f : Submodule.span ℤ (Irr G)) : G → ℂ) = (ν f : G → ℂ) := (rfl)

noncomputable def dadeBetaCoeff (A : Set G) (R : G → Subgroup G) (H : Subgroup ↥L)
    (ξ : ι → (↥L → ℂ)) (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) : ℂ :=
  cfInner (dadeBeta A R H (ξ k₀)) (coherentImage ξ ν k₀) + 1

omit [H.Normal] [Fintype ι] in
theorem cfInner_dadeBeta_coherentImage_self :
    cfInner (dadeBeta A R H (ξ k₀)) (coherentImage ξ ν k₀) = dadeBetaCoeff A R H ξ ν k₀ - 1 := by
  rw [dadeBetaCoeff]; ring

noncomputable def dadeBetaRemainder (A : Set G) (R : G → Subgroup G) (H : Subgroup ↥L)
    (ξ : ι → (↥L → ℂ)) (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) (k₀ : ι) : G → ℂ :=
  dadeBeta A R H (ξ k₀) - ((1 : G → ℂ) - coherentImage ξ ν k₀
    + dadeBetaCoeff A R H ξ ν k₀ • weightedCoherentSum ξ ν (H.index : ℂ))

omit [H.Normal] in
theorem dadeBetaRemainder_apply :
    dadeBetaRemainder A R H ξ ν k₀ = dadeBeta A R H (ξ k₀) - ((1 : G → ℂ) - coherentImage ξ ν k₀
      + dadeBetaCoeff A R H ξ ν k₀ • weightedCoherentSum ξ ν (H.index : ℂ)) := (rfl)

omit [H.Normal] in
theorem dadeBeta_eq_add_dadeBetaRemainder :
    dadeBeta A R H (ξ k₀) = (1 : G → ℂ) - coherentImage ξ ν k₀
      + dadeBetaCoeff A R H ξ ν k₀ • weightedCoherentSum ξ ν (H.index : ℂ)
      + dadeBetaRemainder A R H ξ ν k₀ := by
  rw [dadeBetaRemainder_apply]; ring

section Main

variable (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hinj : Function.Injective ξ)
  (hν : IsCoherentWith (Set.range ξ) τ ν)
  (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ))

omit [Fintype ι] in
include hD hA hS hζ1 in
theorem exists_int_dadeBetaCoeff : ∃ n : ℤ, dadeBetaCoeff A R H ξ ν k₀ = (n : ℂ) := by
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  have hβ : dadeBeta A R H (ξ k₀) ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars (dadeBeta_mem_virtualChars hD hA hζS hζ1)
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hβ (coherentImage_mem_span_Irr k₀)
  exact ⟨m + 1, by rw [dadeBetaCoeff, hm]; push_cast; ring⟩

omit [Fintype ι] in
include hD hA hS hζ1 in
theorem dadeBetaCoeff_mem_range_intCast :
    dadeBetaCoeff A R H ξ ν k₀ ∈ Set.range (fun n : ℤ => (n : ℂ)) := by
  obtain ⟨n, hn⟩ := exists_int_dadeBetaCoeff hD hA hS hζ1
  exact ⟨n, hn.symm⟩

omit [Fintype ι] in
include hD hA hS hτ hζ1 in
theorem cfInner_dadeBeta_baseline (f : charSpanZero (Set.range ξ)) :
    cfInner (dadeBeta A R H (ξ k₀)) (τ f : G → ℂ)
      = cfInner (indClassFun H (1 : ↥H → ℂ) - ξ k₀) (f : ↥L → ℂ) := by
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  have hdom : indClassFun H (1 : ↥H → ℂ) - ξ k₀ ∈ dadeDomain L A :=
    indClassFun_one_sub_mem_dadeDomain hA hζS hζ1
  have hSsub : Set.range ξ ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset
  have hf := mem_charSpanZero.1 f.2
  have hfdom : (f : ↥L → ℂ) ∈ dadeDomain L A :=
    mem_dadeDomain_of_mem_span_indFam hA hSsub hf.1 hf.2
  rw [dadeBeta_eq_dadeMap hD hdom, hτ f ⟨_, hfdom⟩ rfl,
    cfInner_dadeMap hD ⟨_, hdom⟩ ⟨_, hfdom⟩]

omit [Fintype ι] in
open scoped Classical in
include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem cfInner_dadeBeta_coherentImage (l : ι) :
    cfInner (dadeBeta A R H (ξ k₀)) (coherentImage ξ ν l)
      = dadeBetaCoeff A R H ξ ν k₀ * (ξ l 1 / (H.index : ℂ)) - (if k₀ = l then 1 else 0) := by
  have hidx : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  have hSsub : Set.range ξ ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset
  obtain ⟨d, -, hdvd, hd⟩ := exists_apply_one_eq_of_mem_indFam H (hSsub ⟨l, rfl⟩)
  obtain ⟨m, rfl⟩ := hdvd
  have hml : ξ l 1 = (m : ℂ) * (H.index : ℂ) := by rw [hd]; push_cast; ring
  have hmdiv : ξ l 1 / (H.index : ℂ) = (m : ℂ) := by rw [hml]; field_simp
  set u : Submodule.span ℤ (Set.range ξ) := ⟨ξ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩ with hu
  set v : Submodule.span ℤ (Set.range ξ) := ⟨ξ l, Submodule.subset_span ⟨l, rfl⟩⟩ with hv
  set g : Submodule.span ℤ (Set.range ξ) := v - (m : ℤ) • u with hg
  have hgcoe : (g : ↥L → ℂ) = ξ l - (m : ℂ) • ξ k₀ := by
    have h1 : (g : ↥L → ℂ) = (v : ↥L → ℂ) - (m : ℤ) • (u : ↥L → ℂ) := by rw [hg]; rfl
    rw [h1, ← Int.cast_smul_eq_zsmul ℂ (m : ℤ)]
    push_cast
    rfl
  have hg1 : (g : ↥L → ℂ) 1 = 0 := by
    rw [hgcoe]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hml, hζ1]
    ring
  set f₀ : charSpanZero (Set.range ξ) := ⟨(g : ↥L → ℂ), mem_charSpanZero.2 ⟨g.2, hg1⟩⟩ with hf₀
  have hincl : Submodule.inclusion (charSpanZero_le (Set.range ξ)) f₀ = g := Subtype.ext rfl
  have hνg : (ν g : G → ℂ) = (τ f₀ : G → ℂ) := by rw [← hincl, hν.eq_on_zero f₀]
  have hleft : cfInner (dadeBeta A R H (ξ k₀)) (ν g : G → ℂ)
      = (m : ℂ) - (if k₀ = l then 1 else 0) := by
    rw [hνg, cfInner_dadeBeta_baseline hD hA hS hτ hζ1 f₀]
    change cfInner (indClassFun H (1 : ↥H → ℂ) - ξ k₀) (g : ↥L → ℂ) = _
    rw [hgcoe, cfInner_sub_right, cfInner_smul_right,
      cfInner_indClassFun_one_sub_of_mem_range hinj hS hζIrr l,
      cfInner_indClassFun_one_sub_of_mem_range hinj hS hζIrr k₀, if_pos rfl]
    simp
    ring
  have hright : cfInner (dadeBeta A R H (ξ k₀)) (ν g : G → ℂ)
      = cfInner (dadeBeta A R H (ξ k₀)) (coherentImage ξ ν l)
        - (m : ℂ) * cfInner (dadeBeta A R H (ξ k₀)) (coherentImage ξ ν k₀) := by
    have hc : (ν g : G → ℂ) = (ν v : G → ℂ) - (m : ℂ) • (ν u : G → ℂ) := by
      have h1 : (ν g : G → ℂ) = (ν v : G → ℂ) - (m : ℤ) • (ν u : G → ℂ) := by
        rw [hg, map_sub, map_zsmul]; rfl
      rw [h1, ← Int.cast_smul_eq_zsmul ℂ (m : ℤ)]
      push_cast
      rfl
    rw [hc, cfInner_sub_right, cfInner_smul_right, coherentImage_apply, coherentImage_apply,
      hu, hv]
    simp
  rw [hmdiv, dadeBetaCoeff]
  linear_combination -(hleft.symm.trans hright)

omit [Fintype ι] in
include hD hν hτ in
theorem coherentHomSpan_eq_dadeMap (f : Submodule.span ℤ (Set.range ξ)) (F : dadeDomain L A)
    (h : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    ((coherentHomSpan ν f : Submodule.span ℤ (Irr G)) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have hF1 : (F : ↥L → ℂ) 1 = 0 :=
    dadeDomain.apply_eq_zero F.2 (by simpa using hD.one_notMem)
  have hf1 : (f : ↥L → ℂ) 1 = 0 := by rw [h, hF1]
  set f₀ : charSpanZero (Set.range ξ) := ⟨(f : ↥L → ℂ), mem_charSpanZero.2 ⟨f.2, hf1⟩⟩ with hf₀
  have hincl : Submodule.inclusion (charSpanZero_le (Set.range ξ)) f₀ = f := Subtype.ext rfl
  rw [coherentHomSpan_coe, ← hincl, hν.eq_on_zero f₀, hτ f₀ F h]

omit [Fintype ι] in
include hD hA hS hν hτ hζIrr hζ1 in
theorem cfInner_coherentImage_one (hS2 : (Set.range ξ).Nontrivial) (l : ι) :
    cfInner (coherentImage ξ ν l) (1 : G → ℂ) = 0 := by
  have key := cfInner_one_eq_zero_of_mem_indFam_sdiff (ν := coherentHomSpan ν) hD hA hS
    (fun f h => by rw [coherentHomSpan_coe, coherentHomSpan_coe]; exact hν.inner_eq f h)
    (fun f F h => coherentHomSpan_eq_dadeMap hD hν hτ f F h)
    (Set.mem_range_self k₀) hζIrr hζ1 hS2 (Set.mem_range_self l)
  rw [coherentHomSpan_coe] at key
  rw [coherentImage_apply]
  exact key

omit [H.Normal] in
theorem cfInner_weightedCoherentSum_one
    (hone : ∀ l : ι, cfInner (coherentImage ξ ν l) (1 : G → ℂ) = 0) :
    cfInner (weightedCoherentSum ξ ν (H.index : ℂ)) (1 : G → ℂ) = 0 := by
  rw [weightedCoherentSum_apply, cfInner_sum_left]
  exact Finset.sum_eq_zero fun l _ => by rw [cfInner_smul_left, hone l, mul_zero]

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem cfInner_dadeBetaRemainder_coherentImage (hS2 : (Set.range ξ).Nontrivial) (l : ι) :
    cfInner (dadeBetaRemainder A R H ξ ν k₀) (coherentImage ξ ν l) = 0 := by
  classical
  have hone := cfInner_coherentImage_one hD hA hS hν hτ hζIrr hζ1 hS2
  have hidx : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  have h1 : cfInner (1 : G → ℂ) (coherentImage ξ ν l) = 0 := by
    rw [← conj_cfInner, hone l, map_zero]
  have h3 : cfInner (weightedCoherentSum ξ ν (H.index : ℂ)) (coherentImage ξ ν l)
      = ξ l 1 / (H.index : ℂ) :=
    NormalInducedWeightedNorm.cfInner_weightedCoherentSum_coherentImage H hinj hS hν l
  rw [dadeBetaRemainder_apply, cfInner_sub_left, cfInner_add_left, cfInner_sub_left,
    cfInner_smul_left, h1, h3,
    cfInner_dadeBeta_coherentImage hD hA hS hinj hν hτ hζIrr hζ1 l]
  by_cases hkl : k₀ = l
  · subst hkl
    have h2 : cfInner (coherentImage ξ ν k₀) (coherentImage ξ ν k₀) = 1 := by
      rw [NormalInducedWeightedNorm.cfInner_coherentImage_eq_ite H hinj hS hν k₀ k₀, if_pos rfl,
        cfInner_self_of_mem_Irr hζIrr]
    rw [h2, if_pos rfl, hζ1, div_self hidx]
    ring
  · have h2 : cfInner (coherentImage ξ ν k₀) (coherentImage ξ ν l) = 0 := by
      rw [NormalInducedWeightedNorm.cfInner_coherentImage_eq_ite H hinj hS hν k₀ l, if_neg hkl]
    rw [h2, if_neg hkl]
    ring

include hD hA hS hν hτ hζIrr hζ1 in
theorem cfInner_dadeBetaRemainder_one (hS2 : (Set.range ξ).Nontrivial) :
    cfInner (dadeBetaRemainder A R H ξ ν k₀) (1 : G → ℂ) = 0 := by
  have hone := cfInner_coherentImage_one hD hA hS hν hτ hζIrr hζ1 hS2
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  rw [dadeBetaRemainder_apply, cfInner_sub_left, cfInner_add_left, cfInner_sub_left,
    cfInner_smul_left, cfInner_dadeBeta_one hD hA hζS hζ1, hone k₀,
    cfInner_weightedCoherentSum_one hone, cfInner_one_one]
  ring

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem dadeBetaProjection_spec (hS2 : (Set.range ξ).Nontrivial) :
    (∃ n : ℤ, dadeBetaCoeff A R H ξ ν k₀ = (n : ℂ)) ∧
      dadeBeta A R H (ξ k₀) = (1 : G → ℂ) - coherentImage ξ ν k₀
        + dadeBetaCoeff A R H ξ ν k₀ • weightedCoherentSum ξ ν (H.index : ℂ)
        + dadeBetaRemainder A R H ξ ν k₀ ∧
      (∀ l : ι, IsOrthogonal (dadeBetaRemainder A R H ξ ν k₀) (coherentImage ξ ν l)) ∧
      IsOrthogonal (dadeBetaRemainder A R H ξ ν k₀) (1 : G → ℂ) :=
  ⟨exists_int_dadeBetaCoeff hD hA hS hζ1, dadeBeta_eq_add_dadeBetaRemainder,
    fun l => isOrthogonal_iff.2
      (cfInner_dadeBetaRemainder_coherentImage hD hA hS hinj hν hτ hζIrr hζ1 hS2 l),
    isOrthogonal_iff.2 (cfInner_dadeBetaRemainder_one hD hA hS hν hτ hζIrr hζ1 hS2)⟩

end Main

end NormalInducedFamily

end CFSG.FeitThompson
