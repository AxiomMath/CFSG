module

public import CFSG.FeitThompson.Representations.DadeBetaProjectionIntegralParameter
public import CFSG.FeitThompson.Definitions.DadeAveragingMap
import CFSG.FeitThompson.Representations.OrthogonalRemainderExactNorm
import CFSG.FeitThompson.Representations.LargeKernelProjectionParameterVanishes
import CFSG.FeitThompson.Representations.InverseDadeInducedBasisExpansion
import CFSG.FeitThompson.Representations.RegularCharOrthogonalInducedBasis
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate
open CrossFamilyProjection (coherentImage coherentImage_apply)

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {ι : Type*} [Finite ι] {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

omit [Fintype G] [Finite ι] [H.Normal] [Fintype ↥L] in
theorem sdiff_eq_of_image_sdiff_eq
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) :
    A = ((H.map L.subtype : Subgroup G) : Set G) \ {1} := by
  rw [hA, Subgroup.coe_map]
  ext g
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun h => hx1 (by exact_mod_cast Subtype.ext h)⟩
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    exact ⟨x, ⟨hx, fun h => hne (by rw [h]; rfl)⟩, rfl⟩

section Main

variable (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hinj : Function.Injective ξ)
  (hν : IsCoherentWith (Set.range ξ) τ ν)
  (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ))

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem dadeBetaCoeff_eq_zero (hS2 : (Set.range ξ).Nontrivial)
    {p : ℤ} (hp : 3 ≤ p) (hh : p ^ 2 ≤ (Nat.card ↥H : ℤ))
    (hep : 2 * (H.index : ℤ) ≤ p + 1) :
    dadeBetaCoeff A R H ξ ν k₀ = 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, hn⟩ := exists_int_dadeBetaCoeff hD hA hS hζ1
  have he : 1 ≤ (H.index : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hnn := cfInner_self_nonneg (dadeBetaRemainder A R H ξ ν k₀)
  rw [cfInner_self_dadeBetaRemainder hD hA hS hinj hν hτ hζIrr hζ1 hS2, hn] at hnn
  have hcast : (((H.index : ℝ) - 1 + 2 * (n : ℝ)
      - (n : ℝ) ^ 2 * (((Nat.card ↥H : ℝ) - 1) / (H.index : ℝ)) : ℝ) : ℂ)
      = (H.index : ℂ) - 1 + 2 * (n : ℂ)
        - (n : ℂ) ^ 2 * (((Nat.card ↥H : ℂ) - 1) / (H.index : ℂ)) := by
    push_cast
    ring
  rw [← hcast] at hnn
  have key := Complex.zero_le_real.1 hnn
  have hzero : n = 0 := by
    refine eq_zero_of_sq_mul_sub_one_div_sub_two_mul_le hp he hh hep ?_
    rw [mul_div_assoc]
    push_cast
    linarith [key]
  rw [hn, hzero, Int.cast_zero]

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem cfInner_dadeBeta_coherentImage_eq_neg_one (hS2 : (Set.range ξ).Nontrivial)
    {p : ℤ} (hp : 3 ≤ p) (hh : p ^ 2 ≤ (Nat.card ↥H : ℤ))
    (hep : 2 * (H.index : ℤ) ≤ p + 1) :
    cfInner (dadeBeta A R H (ξ k₀)) (coherentImage ξ ν k₀) = -1 := by
  rw [cfInner_dadeBeta_coherentImage_self,
    dadeBetaCoeff_eq_zero hD hA hS hinj hν hτ hζIrr hζ1 hS2 hp hh hep]
  ring

omit [Finite ι] in
include hD hA hS hν hτ hζIrr hζ1 in
theorem cfInner_dadeMap_coherentImage_of_mem_indFam
    (ha : dadeBetaCoeff A R H ξ ν k₀ = 0)
    {f : ↥L → ℂ} (hf : f ∈ indFam H (Irr ↥H)) (hne : f ≠ ξ k₀)
    (F : dadeDomain L A) (hF : (F : ↥L → ℂ) = f - (f 1 / (H.index : ℂ)) • ξ k₀) :
    cfInner ((dadeMap hD F : classFun G) : G → ℂ) (coherentImage ξ ν k₀)
      = -(f 1 / (H.index : ℂ)) := by
  have hidx : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  have hζT : ξ k₀ ∈ indFam H (Irr ↥H) := indFam_mono H Set.sdiff_subset hζS
  by_cases hfS : f ∈ indFam H (Irr ↥H \ {1})
  ·
    obtain ⟨l, hl⟩ : ∃ l, ξ l = f := by rw [← hS] at hfS; exact hfS
    obtain ⟨d, -, hdvd, hd⟩ := exists_apply_one_eq_of_mem_indFam H hf
    obtain ⟨m, rfl⟩ := hdvd
    have hml : f 1 = (m : ℂ) * (H.index : ℂ) := by rw [hd]; push_cast; ring
    have hmdiv : f 1 / (H.index : ℂ) = (m : ℂ) := by rw [hml]; field_simp
    set u : Submodule.span ℤ (Set.range ξ) := ⟨ξ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩ with hu
    set v : Submodule.span ℤ (Set.range ξ) := ⟨f, Submodule.subset_span ⟨l, hl⟩⟩ with hv
    set g : Submodule.span ℤ (Set.range ξ) := v - (m : ℤ) • u with hg
    have hgcoe : (g : ↥L → ℂ) = f - (m : ℂ) • ξ k₀ := by
      have h1 : (g : ↥L → ℂ) = (v : ↥L → ℂ) - (m : ℤ) • (u : ↥L → ℂ) := by rw [hg]; rfl
      rw [h1, ← Int.cast_smul_eq_zsmul ℂ (m : ℤ)]
      push_cast
      rfl
    have hg1 : (g : ↥L → ℂ) 1 = 0 := by
      rw [hgcoe]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hml, hζ1]
      ring
    have hFcoe : (g : ↥L → ℂ) = (F : ↥L → ℂ) := by rw [hgcoe, hF, hmdiv]
    set f₀ : charSpanZero (Set.range ξ) := ⟨(g : ↥L → ℂ), mem_charSpanZero.2 ⟨g.2, hg1⟩⟩ with hf₀
    have hincl : Submodule.inclusion (charSpanZero_le (Set.range ξ)) f₀ = g := Subtype.ext rfl
    have hνg : (ν g : G → ℂ) = (τ f₀ : G → ℂ) := by rw [← hincl, hν.eq_on_zero f₀]
    rw [← hτ f₀ F hFcoe, ← hνg, coherentImage_apply]
    have hueq : (ν u : G → ℂ) = (ν ⟨ξ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩ : G → ℂ) := rfl
    rw [← hueq, hν.inner_eq g u, hgcoe, hu]
    change cfInner (f - (m : ℂ) • ξ k₀) (ξ k₀) = _
    rw [cfInner_sub_left, cfInner_smul_left,
      cfInner_eq_zero_of_mem_indFam H hf hζT hne, cfInner_self_of_mem_Irr hζIrr, hmdiv]
    ring
  ·
    have hfT : f ∉ indFam H (Irr ↥H) \ {indClassFun H (1 : ↥H → ℂ)} := by
      rw [indFam_diff_singleton]; exact hfS
    have hfη : f = indClassFun H (1 : ↥H → ℂ) := by
      by_contra hc
      exact hfT ⟨hf, hc⟩
    have hf1 : f 1 = (H.index : ℂ) := by
      rw [hfη]; exact NormalInducedWeightedNorm.indClassFun_one_apply_one H
    have hβdom : indClassFun H (1 : ↥H → ℂ) - ξ k₀ ∈ dadeDomain L A :=
      indClassFun_one_sub_mem_dadeDomain hA hζS hζ1
    have hFeq : F = (⟨indClassFun H (1 : ↥H → ℂ) - ξ k₀, hβdom⟩ : dadeDomain L A) := by
      refine Subtype.ext ?_
      rw [hF, hf1, div_self hidx, one_smul, hfη]
    rw [hFeq, ← dadeBeta_eq_dadeMap hD hβdom, cfInner_dadeBeta_coherentImage_self, ha, hf1,
      div_self hidx]
    ring

omit [Finite ι] in
include hD hA hS hν hτ hζIrr hζ1 in
theorem dadeAverage_coherentImage_eq (ha : dadeBetaCoeff A R H ξ ν k₀ = 0)
    {x : ↥L} (hx : x ∈ H) (hx1 : x ≠ 1) :
    dadeAverage A R (coherentImage ξ ν k₀) (x : G) = ξ k₀ x := by
  classical
  have : Fintype (indFam H (Irr ↥H)) := Fintype.ofFinite _
  have hidx : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  have hζT : ξ k₀ ∈ indFam H (Irr ↥H) := indFam_mono H Set.sdiff_subset hζS
  set A' := sdiff_eq_of_image_sdiff_eq hA with hA'
  set ξ₀ : indFam H (Irr ↥H) := ⟨ξ k₀, hζT⟩ with hξ₀
  have hΨ : (coherentImage ξ ν k₀) ∈ classFun G := by
    rw [coherentImage_apply]
    exact virtualChars_le_classFun (ν _).2
  rw [dadeAverage_eq_sum_conj_cfInner_dadeMap_puncturedDiff' hD A' hΨ ξ₀ hx hx1]
  set n : indFam H (Irr ↥H) → ℂ := fun f => cfInner (f : ↥L → ℂ) (f : ↥L → ℂ) with hn
  have hterm : ∀ f ∈ Finset.univ.erase ξ₀,
      conj (cfInner ((dadeMap hD (puncturedDiffDade A' ξ₀ f) : classFun G) : G → ℂ)
          (coherentImage ξ ν k₀)) * (f : ↥L → ℂ) x / n f
        = -((H.index : ℂ)⁻¹ * (((f : ↥L → ℂ) 1 / n f) * (f : ↥L → ℂ) x)) := by
    intro f hfmem
    have hfne : (f : ↥L → ℂ) ≠ ξ k₀ := by
      intro h
      exact (Finset.mem_erase.1 hfmem).1 (Subtype.ext h)
    have hFcoe : ((puncturedDiffDade A' ξ₀ f : dadeDomain L A) : ↥L → ℂ)
        = (f : ↥L → ℂ) - ((f : ↥L → ℂ) 1 / (H.index : ℂ)) • ξ k₀ := by
      rw [coe_puncturedDiffDade, puncturedDiff_eq]
      change (f : ↥L → ℂ) - ((f : ↥L → ℂ) 1 / (ξ k₀) 1) • ξ k₀ = _
      rw [hζ1]
    rw [cfInner_dadeMap_coherentImage_of_mem_indFam hD hA hS hν hτ hζIrr hζ1 ha f.2 hfne _ hFcoe,
      map_neg, map_div₀, conj_apply_one_of_mem_indFam H f.2, Complex.conj_natCast]
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hreg : ∑ f : indFam H (Irr ↥H), ((f : ↥L → ℂ) 1 / n f) * (f : ↥L → ℂ) x = 0 := by
    have h := congrFun (leftRegular_character_eq_sum_indFam (L := ↥L) H) x
    rw [leftRegular_character_of_ne_one hx1] at h
    have h2 : (0 : ℂ) = ∑ f : indFam H (Irr ↥H), ((f : ↥L → ℂ) 1 / n f) * (f : ↥L → ℂ) x := by
      rw [h]; simp [hn]
    exact h2.symm
  have herase : ∑ f ∈ Finset.univ.erase ξ₀, ((f : ↥L → ℂ) 1 / n f) * (f : ↥L → ℂ) x
      = -(((ξ k₀) 1 / n ξ₀) * (ξ k₀) x) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (indFam H (Irr ↥H)))
      (fun f : indFam H (Irr ↥H) => ((f : ↥L → ℂ) 1 / n f) * (f : ↥L → ℂ) x)
      (Finset.mem_univ ξ₀)
    rw [hreg] at h
    change _ + (((ξ k₀) 1 / n ξ₀) * (ξ k₀) x) = 0 at h
    linear_combination h
  have hnζ : n ξ₀ = 1 := by
    change cfInner (ξ k₀) (ξ k₀) = 1
    exact cfInner_self_of_mem_Irr hζIrr
  rw [herase, hnζ, hζ1]
  field_simp

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem dadeInverseRecovery_spec (hS2 : (Set.range ξ).Nontrivial)
    {p : ℤ} (hp : 3 ≤ p) (hh : p ^ 2 ≤ (Nat.card ↥H : ℤ))
    (hep : 2 * (H.index : ℤ) ≤ p + 1) :
    dadeBetaCoeff A R H ξ ν k₀ = 0 ∧
      cfInner (dadeBeta A R H (ξ k₀)) (coherentImage ξ ν k₀) = -1 ∧
      ∀ x : ↥L, x ∈ H → x ≠ 1 →
        dadeAverage A R (coherentImage ξ ν k₀) (x : G) = ξ k₀ x :=
  ⟨dadeBetaCoeff_eq_zero hD hA hS hinj hν hτ hζIrr hζ1 hS2 hp hh hep,
    cfInner_dadeBeta_coherentImage_eq_neg_one hD hA hS hinj hν hτ hζIrr hζ1 hS2 hp hh hep,
    fun _x hx hx1 => dadeAverage_coherentImage_eq hD hA hS hν hτ hζIrr hζ1
      (dadeBetaCoeff_eq_zero hD hA hS hinj hν hτ hζIrr hζ1 hS2 hp hh hep) hx hx1⟩

end Main

end NormalInducedFamily

end CFSG.FeitThompson
