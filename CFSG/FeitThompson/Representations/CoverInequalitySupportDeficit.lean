module

public import CFSG.FeitThompson.Representations.DadeInverseConstantOffExceptionalFamily
public import CFSG.FeitThompson.Representations.NormInequalityDisjointDadeSupports
public import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
import CFSG.FeitThompson.Representations.DadeIntegerParameterNormBounds
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.WitnessCongruenceLocalInverseNormBound
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace MultipleCoverDeficit

open NormalInducedFamily
open CrossFamilyProjection (coherentImage coherentImage_apply)
open DisjointCoherentFamilies (IsFullCoherentFamily isFullCoherentFamily_of_isDadeData
  cfInner_coherentImage_coherentImage_eq_zero_of_ne)

section Reindex

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {ι : Type*} {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G}

omit [Fintype G] [H.Normal] in
theorem span_indFam_le_span_range (hS : Set.range ξ = indFam H (Irr ↥H \ {1})) :
    Submodule.span ℤ (indFam H (Irr ↥H \ {1})) ≤ Submodule.span ℤ (Set.range ξ) :=
  le_of_eq (by rw [hS])

omit [Fintype G] [H.Normal] in
theorem charSpanZero_indFam_le (hS : Set.range ξ = indFam H (Irr ↥H \ {1})) :
    charSpanZero (indFam H (Irr ↥H \ {1})) ≤ charSpanZero (Set.range ξ) :=
  le_of_eq (by rw [hS])

noncomputable def setIndexedHom (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G) :
    Submodule.span ℤ (indFam H (Irr ↥H \ {1})) →+ virtualChars G :=
  ν.comp (Submodule.inclusion (span_indFam_le_span_range hS)).toAddMonoidHom

omit [Fintype G] [H.Normal] in
theorem coe_setIndexedHom (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (f : Submodule.span ℤ (indFam H (Irr ↥H \ {1}))) :
    (setIndexedHom hS ν f : G → ℂ)
      = (ν ⟨(f : ↥L → ℂ), span_indFam_le_span_range hS f.2⟩ : G → ℂ) := (rfl)

omit [Fintype G] [H.Normal] in
theorem coe_setIndexedHom_eq_coherentImage (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (l : ι) (hl : ξ l ∈ indFam H (Irr ↥H \ {1})) :
    (setIndexedHom hS ν ⟨ξ l, Submodule.subset_span hl⟩ : G → ℂ)
      = coherentImage ξ ν l := by
  rw [coe_setIndexedHom, coherentImage_apply]

theorem isCoherentWith_setIndexedHom (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ)) :
    IsCoherentWith (indFam H (Irr ↥H \ {1})) (nonprincipalBaselineHom hD hA)
      (setIndexedHom hS ν) where
  inner_eq f h := by
    rw [coe_setIndexedHom, coe_setIndexedHom, hν.inner_eq]
  eq_on_zero f := by
    refine Subtype.ext ?_
    have hmem : (f : ↥L → ℂ) ∈ dadeDomain L A :=
      NormalInducedFamily.mem_dadeDomain_of_mem_span_indFam hA
        (indFam_mono H Set.sdiff_subset) (charSpanZero_le _ f.2) (charSpanZero_apply_one f)
    set F : dadeDomain L A := ⟨(f : ↥L → ℂ), hmem⟩ with hF
    set f' : charSpanZero (Set.range ξ) :=
      ⟨(f : ↥L → ℂ), charSpanZero_indFam_le hS f.2⟩ with hf'
    have h1 : ((setIndexedHom hS ν
        (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = (ν (Submodule.inclusion (charSpanZero_le (Set.range ξ)) f') : G → ℂ) := rfl
    rw [h1, hν.eq_on_zero f', hτ f' F rfl, coe_nonprincipalBaselineHom hD hA f F rfl]

end Reindex

section Signed

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal]
  {ν : Submodule.span ℤ (indFam H (Irr ↥H \ {1})) →+ virtualChars G}
  {χ : G → ℂ} {ζ : ↥L → ℂ}

theorem cfInner_self_dadeAverage_of_mem_signedIrr (hD : IsDadeData L A R)
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
    (hν : IsCoherentWith (indFam H (Irr ↥H \ {1})) (nonprincipalBaselineHom hD hA) ν)
    (hχ : χ ∈ signedIrr G)
    (hperp : ∀ f, ∀ hf : f ∈ indFam H (Irr ↥H \ {1}),
      cfInner χ (ν ⟨f, Submodule.subset_span hf⟩ : G → ℂ) = 0)
    (hζS : ζ ∈ indFam H (Irr ↥H \ {1})) (hζ1 : ζ 1 = (H.index : ℂ)) :
    cfInner (fun y : ↥L => dadeAverage A R χ (y : G))
        (fun y : ↥L => dadeAverage A R χ (y : G))
      = ((Nat.card ↥H : ℂ) - 1) / ((H.index : ℂ) * (Nat.card ↥H : ℂ))
          * cfInner (dadeBeta A R H ζ) χ ^ 2 := by
  obtain ⟨ε, hε, η, hηIrr, hχη⟩ := mem_signedIrr_iff_exists_sign.1 hχ
  have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have hεsq : ε * (starRingEnd ℂ) ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεconj : ((starRingEnd ℂ) ε) ^ 2 = 1 := by rcases hε with rfl | rfl <;> simp
  have hperpη : ∀ f, ∀ hf : f ∈ indFam H (Irr ↥H \ {1}),
      cfInner η (ν ⟨f, Submodule.subset_span hf⟩ : G → ℂ) = 0 := by
    intro f hf
    have h := hperp f hf
    rw [hχη, cfInner_smul_left] at h
    exact (mul_eq_zero.1 h).resolve_left hεne
  have key := cfInner_self_dadeAverage hD hA hν hηIrr hperpη hζS hζ1
  have hres : (fun y : ↥L => dadeAverage A R χ (y : G))
      = ε • (fun y : ↥L => dadeAverage A R η (y : G)) := by
    funext y
    rw [hχη, dadeAverage_smul]
    rfl
  rw [hres, cfInner_smul_left, cfInner_smul_right, key, hχη, cfInner_smul_right, mul_pow,
    hεconj]
  linear_combination (((Nat.card ↥H : ℂ) - 1) / ((H.index : ℂ) * (Nat.card ↥H : ℂ))
    * cfInner (dadeBeta A R H ζ) η ^ 2) * hεsq

end Signed

section Elementary

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : Subgroup ↥L}

theorem ncard_eq_of_eq_image [Finite G]
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) :
    A.ncard = Nat.card ↥H - 1 := by
  rw [hA, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_sdiff_singleton_of_mem (a := (1 : ↥L)) (by simp), ← Nat.card_coe_set_eq]
  rfl

theorem natCard_subgroup_eq [Finite G] :
    (Nat.card ↥L : ℝ) = (H.index : ℝ) * (Nat.card ↥H : ℝ) := by
  rw [← Nat.cast_mul, H.index_mul_card]

theorem ncard_div_natCard_eq [Finite G]
    (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})) :
    (A.ncard : ℝ) / (Nat.card ↥L : ℝ)
      = ((Nat.card ↥H : ℝ) - 1) / ((H.index : ℝ) * (Nat.card ↥H : ℝ)) := by
  rw [ncard_eq_of_eq_image hA, natCard_subgroup_eq (L := L) (H := H),
    Nat.cast_sub Nat.card_pos]
  norm_num

theorem measure_nonneg [Finite G] :
    0 ≤ ((Nat.card ↥H : ℝ) - 1) / ((H.index : ℝ) * (Nat.card ↥H : ℝ)) := by
  have h1 : (1 : ℝ) ≤ (Nat.card ↥H : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.card_pos (α := ↥H)).ne'
  have h2 : (0 : ℝ) ≤ (H.index : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ (Nat.card ↥H : ℝ) := Nat.cast_nonneg _
  exact div_nonneg (by linarith) (by positivity)

end Elementary

section Degree

variable {G : Type*} [Group G]

theorem one_le_norm_apply_one_of_mem_signedIrr {χ : G → ℂ} (hχ : χ ∈ signedIrr G) :
    1 ≤ ‖χ 1‖ := by
  obtain ⟨ε, hε, η, hηIrr, rfl⟩ := mem_signedIrr_iff_exists_sign.1 hχ
  obtain ⟨d, hd, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hηIrr
  have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, hεn, one_mul, hd1, Complex.norm_natCast]
  exact_mod_cast hd

theorem one_le_sum_norm_sq_of_mem_signedIrr {χ : G → ℂ} (hχ : χ ∈ signedIrr G)
    {F : Finset G} (h1 : (1 : G) ∈ F) : 1 ≤ ∑ g ∈ F, ‖χ g‖ ^ 2 := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun g => ‖χ g‖ ^ 2)
    (fun g _ => sq_nonneg _) h1)
  nlinarith [one_le_norm_apply_one_of_mem_signedIrr hχ]

end Degree

section Main

variable {G : Type*} [Group G] [Fintype G] {I : Type*} [Fintype I]
  {Lsub : I → Subgroup G} [∀ i, Fintype ↥(Lsub i)] {A : I → Set G} {J : I → G → Subgroup G}
  {H : ∀ i, Subgroup ↥(Lsub i)} [∀ i, (H i).Normal]
  {ι : I → Type*} [∀ i, Fintype (ι i)] {ξ : ∀ i, ι i → (↥(Lsub i) → ℂ)} {k₀ : ∀ i, ι i}
  {τ : ∀ i, charSpanZero (Set.range (ξ i)) →+ virtualChars G}
  {ν : ∀ i, Submodule.span ℤ (Set.range (ξ i)) →+ virtualChars G}

variable (hodd : Odd (Nat.card G))
  (hDade : ∀ i, IsDadeData (Lsub i) (A i) (J i))
  (hA : ∀ i, A i = (fun x : ↥(Lsub i) => (x : G)) '' (((H i) : Set ↥(Lsub i)) \ {1}))
  (hS : ∀ i, Set.range (ξ i) = indFam (H i) (Irr ↥(H i) \ {1}))
  (hinj : ∀ i, Function.Injective (ξ i))
  (hSIrr : ∀ i, Set.range (ξ i) ⊆ Irr ↥(Lsub i))
  (hν : ∀ i, IsCoherentWith (Set.range (ξ i)) (τ i) (ν i))
  (hτ : ∀ i, ∀ (f : charSpanZero (Set.range (ξ i))) (F : dadeDomain (Lsub i) (A i)),
    (f : ↥(Lsub i) → ℂ) = (F : ↥(Lsub i) → ℂ) →
      (τ i f : G → ℂ) = ((dadeMap (hDade i) F : classFun G) : G → ℂ))
  (hζ1 : ∀ i, ξ i (k₀ i) 1 = ((H i).index : ℂ))
  (hdisj : Pairwise fun i j =>
    Disjoint (totalDadeSupport (A i) (J i)) (totalDadeSupport (A j) (J j)))
  (hbound : ∀ i, 2 * (H i).index + 1 ≤ Nat.card ↥(H i))

omit [Fintype I] [∀ i, Fintype (ι i)] in
include hodd hDade hA hS hSIrr hν hτ in
theorem isFullCoherentFamily_family (i : I) :
    IsFullCoherentFamily (ξ i) (τ i) (ν i) (totalDadeSupport (A i) (J i)) :=
  isFullCoherentFamily_of_isDadeData hodd (hDade i) (hA i) (hS i) (hSIrr i)
    (fun f hf => hτ i f ⟨(f : ↥(Lsub i) → ℂ), hf⟩ rfl) (hν i)

omit [Fintype I] [∀ i, Fintype (ι i)] in
include hodd hDade hA hS hSIrr hν hτ in
theorem nontrivial_range (i : I) (k : ι i) : (Set.range (ξ i)).Nontrivial :=
  (Set.one_lt_ncard_iff_nontrivial_and_finite.1
    (lt_of_lt_of_le Nat.one_lt_two
      ((isFullCoherentFamily_family hodd hDade hA hS hSIrr hν hτ i).two_le_ncard k))).1

omit [Fintype I] in
include hSIrr hν hinj in
theorem coherentImage_mem_signedIrr (i : I) :
    coherentImage (ξ i) (ν i) (k₀ i) ∈ signedIrr G := by
  refine mem_signedIrr_iff_mem_span_Irr_and_cfInner_self_eq_one.2 ⟨?_, ?_⟩
  · rw [coherentImage_apply]
    exact mem_span_Irr_of_mem_virtualChars (ν i _).2
  · have h := CrossFamilyProjection.cfInner_coherentImage_coherentImage (hinj i)
      (fun k => hSIrr i ⟨k, rfl⟩) (hν i) (k₀ i) (k₀ i)
    simpa using h

omit [Fintype I] in
include hSIrr hν hinj in
theorem cfInner_self_coherentImage_eq_one (i : I) :
    cfInner (coherentImage (ξ i) (ν i) (k₀ i)) (coherentImage (ξ i) (ν i) (k₀ i)) = 1 :=
  cfInner_self_of_mem_signedIrr (coherentImage_mem_signedIrr hinj hSIrr hν i)

omit [Fintype I] [∀ i, Fintype (ι i)] in
include hSIrr hν hinj in
theorem coherentImage_mem_classFun (i : I) :
    coherentImage (ξ i) (ν i) (k₀ i) ∈ classFun G := by
  rw [coherentImage_apply]
  exact virtualChars_le_classFun (ν i _).2

omit [Fintype I] in
include hodd hDade hA hS hSIrr hν hτ hζ1 hinj hdisj in
theorem cfInner_self_dadeAverage_cross {i j : I} (hij : i ≠ j) :
    cfInner (fun y : ↥(Lsub j) =>
        dadeAverage (A j) (J j) (coherentImage (ξ i) (ν i) (k₀ i)) (y : G))
      (fun y : ↥(Lsub j) =>
        dadeAverage (A j) (J j) (coherentImage (ξ i) (ν i) (k₀ i)) (y : G))
      = ((Nat.card ↥(H j) : ℂ) - 1) / (((H j).index : ℂ) * (Nat.card ↥(H j) : ℂ))
        * cfInner (dadeBeta (A j) (J j) (H j) (ξ j (k₀ j)))
            (coherentImage (ξ i) (ν i) (k₀ i)) ^ 2 := by
  have hfam := isFullCoherentFamily_family hodd hDade hA hS hSIrr hν hτ
  refine cfInner_self_dadeAverage_of_mem_signedIrr (hDade j) (hA j)
    (isCoherentWith_setIndexedHom (hDade j) (hA j) (hS j) (hν j) (hτ j))
    (coherentImage_mem_signedIrr hinj hSIrr hν i) ?_ (by rw [← hS j]; exact ⟨k₀ j, rfl⟩) (hζ1 j)
  intro f hf
  obtain ⟨l, rfl⟩ : ∃ l, ξ j l = f := by rw [← hS j] at hf; exact hf
  rw [coe_setIndexedHom_eq_coherentImage (hS j) l hf]
  exact cfInner_coherentImage_coherentImage_eq_zero_of_ne hfam hdisj hij (k₀ i) l

omit [Fintype I] [∀ i, Fintype (ι i)] in
include hDade hA hS hζ1 in
theorem exists_int_cfInner_dadeBeta_coherentImage (i j : I) :
    ∃ m : ℤ, cfInner (dadeBeta (A j) (J j) (H j) (ξ j (k₀ j)))
      (coherentImage (ξ i) (ν i) (k₀ i)) = (m : ℂ) := by
  refine exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars (dadeBeta_mem_virtualChars (hDade j) (hA j)
      (by rw [← hS j]; exact ⟨k₀ j, rfl⟩) (hζ1 j))) ?_
  rw [coherentImage_apply]
  exact mem_span_Irr_of_mem_virtualChars (ν i _).2

omit [Fintype I] in
include hodd hDade hA hS hSIrr hν hτ hζ1 hinj hdisj in
theorem re_cfInner_self_dadeAverage_cross {i j : I} (hij : i ≠ j) :
    (cfInner (fun y : ↥(Lsub j) =>
        dadeAverage (A j) (J j) (coherentImage (ξ i) (ν i) (k₀ i)) (y : G))
      (fun y : ↥(Lsub j) =>
        dadeAverage (A j) (J j) (coherentImage (ξ i) (ν i) (k₀ i)) (y : G))).re
      = ((Nat.card ↥(H j) : ℝ) - 1) / (((H j).index : ℝ) * (Nat.card ↥(H j) : ℝ))
        * ‖cfInner (dadeBeta (A j) (J j) (H j) (ξ j (k₀ j)))
            (coherentImage (ξ i) (ν i) (k₀ i))‖ ^ 2 := by
  obtain ⟨m, hm⟩ :=
    exists_int_cfInner_dadeBeta_coherentImage (ν := ν) (k₀ := k₀) hDade hA hS hζ1 i j
  rw [cfInner_self_dadeAverage_cross hodd hDade hA hS hinj hSIrr hν hτ hζ1 hdisj hij, hm,
    show (((Nat.card ↥(H j) : ℂ) - 1) / (((H j).index : ℂ) * (Nat.card ↥(H j) : ℂ))
        * (m : ℂ) ^ 2)
      = ((((Nat.card ↥(H j) : ℝ) - 1) / (((H j).index : ℝ) * (Nat.card ↥(H j) : ℝ))
        * (m : ℝ) ^ 2 : ℝ) : ℂ) from by push_cast; ring, Complex.ofReal_re]
  simp [sq_abs]

omit [Fintype I] in
include hodd hDade hA hS hSIrr hν hτ hζ1 hinj hbound in
theorem one_sub_index_div_card_le_re_cfInner_self_dadeAverage (i : I) :
    1 - ((H i).index : ℝ) / (Nat.card ↥(H i) : ℝ)
      ≤ (cfInner (fun y : ↥(Lsub i) =>
          dadeAverage (A i) (J i) (coherentImage (ξ i) (ν i) (k₀ i)) (y : G))
        (fun y : ↥(Lsub i) =>
          dadeAverage (A i) (J i) (coherentImage (ξ i) (ν i) (k₀ i)) (y : G))).re :=
  one_sub_index_div_card_le_cfInner_self_dadeAverage_coherentImage (hDade i) (hA i) (hS i)
    (hinj i) (hν i) (hτ i) (hSIrr i ⟨k₀ i, rfl⟩) (hζ1 i)
    (nontrivial_range hodd hDade hA hS hSIrr hν hτ i (k₀ i)) (hbound i)

omit [Fintype I] in
include hDade hSIrr hν hinj in
theorem one_le_sum_norm_sq_dadeCoverComplement (i : I) :
    (1 : ℝ) ≤ ∑ g ∈ (dadeCoverComplement_finite A J).toFinset,
      ‖coherentImage (ξ i) (ν i) (k₀ i) g‖ ^ 2 := by
  refine one_le_sum_norm_sq_of_mem_signedIrr (coherentImage_mem_signedIrr hinj hSIrr hν i) ?_
  simpa using mem_dadeCoverComplement_iff.2
    fun j => (hDade j).one_notMem_totalDadeSupport

omit [∀ i, Fintype (ι i)] in
include hDade hdisj in
theorem dadeCover_inequality_re (χ : classFun G)
    (hχ : cfInner (χ : G → ℂ) (χ : G → ℂ) = 1) :
    ((∑ g ∈ (dadeCoverComplement_finite A J).toFinset, ‖(χ : G → ℂ) g‖ ^ 2)
          - ((dadeCoverComplement A J).ncard : ℝ)) / (Nat.card G : ℝ)
        + ∑ i, ((cfInner (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))
              (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))).re
            - ((A i).ncard : ℝ) / (Nat.card ↥(Lsub i) : ℝ)) ≤ 0 := by
  have h := dadeCover_inequality hDade hdisj χ hχ
  have hcast : ((∑ g ∈ (dadeCoverComplement_finite A J).toFinset, (‖(χ : G → ℂ) g‖ : ℂ) ^ 2)
          - ((dadeCoverComplement A J).ncard : ℂ)) / (Nat.card G : ℂ)
        + ∑ i, (cfInner (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))
              (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))
            - ((A i).ncard : ℂ) / (Nat.card ↥(Lsub i) : ℂ))
      = ((((∑ g ∈ (dadeCoverComplement_finite A J).toFinset, ‖(χ : G → ℂ) g‖ ^ 2)
          - ((dadeCoverComplement A J).ncard : ℝ)) / (Nat.card G : ℝ)
        + ∑ i, ((cfInner (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))
              (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))).re
            - ((A i).ncard : ℝ) / (Nat.card ↥(Lsub i) : ℝ)) : ℝ) : ℂ) := by
    have hterm : ∀ i : I,
        cfInner (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))
            (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))
          = (((cfInner (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))
              (fun y : ↥(Lsub i) => dadeAverage (A i) (J i) (χ : G → ℂ) (y : G))).re : ℝ) : ℂ) :=
      fun i => by rw [cfInner_self_eq_ofReal, Complex.ofReal_re]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => by rw [hterm i]]
    push_cast
    ring
  rw [hcast] at h
  exact_mod_cast h

include hodd hDade hA hS hSIrr hν hτ hζ1 hinj hdisj hbound in
theorem cover_deficit_bound (i : I) (B : Finset I)
    (hB : ∀ j, j ∈ B ↔ (j ≠ i ∧ cfInner (dadeBeta (A j) (J j) (H j) (ξ j (k₀ j)))
      (coherentImage (ξ i) (ν i) (k₀ i)) = 0)) :
    1 - ((H i).index : ℝ) / (Nat.card ↥(H i) : ℝ)
        - ((Nat.card ↥(H i) : ℝ) - 1) / (((H i).index : ℝ) * (Nat.card ↥(H i) : ℝ))
        - ∑ j ∈ B, ((Nat.card ↥(H j) : ℝ) - 1) / (((H j).index : ℝ) * (Nat.card ↥(H j) : ℝ))
      ≤ (((dadeCoverComplement A J).ncard : ℝ) - 1) / (Nat.card G : ℝ) := by
  classical
  set χ : G → ℂ := coherentImage (ξ i) (ν i) (k₀ i) with hχdef
  set μ : I → ℝ := fun j =>
    ((Nat.card ↥(H j) : ℝ) - 1) / (((H j).index : ℝ) * (Nat.card ↥(H j) : ℝ)) with hμdef
  set Rr : I → ℝ := fun j =>
    (cfInner (fun y : ↥(Lsub j) => dadeAverage (A j) (J j) χ (y : G))
      (fun y : ↥(Lsub j) => dadeAverage (A j) (J j) χ (y : G))).re with hRdef
  set N : ℝ := ((dadeCoverComplement A J).ncard : ℝ) with hNdef
  set S₀ : ℝ := ∑ g ∈ (dadeCoverComplement_finite A J).toFinset, ‖χ g‖ ^ 2 with hSdef
  set c : ℝ := 1 - ((H i).index : ℝ) / (Nat.card ↥(H i) : ℝ) with hcdef
  have hGpos : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hcov := dadeCover_inequality_re hDade hdisj
    ⟨χ, coherentImage_mem_classFun hinj hSIrr hν i⟩
    (cfInner_self_coherentImage_eq_one hinj hSIrr hν i)
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
      rw [ncard_div_natCard_eq (hA j)]] at hcov
  have hcov' : (S₀ - N) / (Nat.card G : ℝ) + ∑ j, (Rr j - μ j) ≤ 0 := hcov
  set lb : I → ℝ := fun j =>
    (if j = i then c - μ i else 0) + (if j ∈ B then -μ j else 0) with hlbdef
  have hiB : i ∉ B := fun h => ((hB i).1 h).1 rfl
  have hlb : ∀ j, lb j ≤ Rr j - μ j := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [hlbdef]
      simp only [if_neg hiB, add_zero, if_pos]
      have h := one_sub_index_div_card_le_re_cfInner_self_dadeAverage hodd hDade hA hS hinj
        hSIrr hν hτ hζ1 hbound j
      rw [hRdef, hcdef]
      simpa using sub_le_sub_right h (μ j)
    · have hRj : Rr j = μ j * ‖cfInner (dadeBeta (A j) (J j) (H j) (ξ j (k₀ j))) χ‖ ^ 2 :=
        re_cfInner_self_dadeAverage_cross hodd hDade hA hS hinj hSIrr hν hτ hζ1 hdisj
          (fun h => hji h.symm)
      have hμ0 : 0 ≤ μ j := measure_nonneg (H := H j)
      by_cases hjB : j ∈ B
      ·
        rw [hlbdef]
        simp only [if_neg hji, if_pos hjB, zero_add]
        have h0 : 0 ≤ Rr j := by rw [hRj]; exact mul_nonneg hμ0 (sq_nonneg _)
        linarith
      ·
        rw [hlbdef]
        simp only [if_neg hji, if_neg hjB, add_zero]
        obtain ⟨m, hm⟩ :=
          exists_int_cfInner_dadeBeta_coherentImage (ν := ν) (k₀ := k₀) hDade hA hS hζ1 i j
        have hne : m ≠ 0 := fun h => hjB ((hB j).2 ⟨hji, by rw [hm, h]; norm_num⟩)
        have hone : (1 : ℝ) ≤ ‖cfInner (dadeBeta (A j) (J j) (H j) (ξ j (k₀ j))) χ‖ ^ 2 := by
          rw [hm, Complex.norm_intCast]
          have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs (by omega)
          have h1' : (1 : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
          rw [show ((|m| : ℤ) : ℝ) = |(m : ℝ)| from by push_cast; ring] at h1'
          nlinarith
        rw [hRj]
        nlinarith
  have hsumlb : ∑ j, lb j = (c - μ i) - ∑ j ∈ B, μ j := by
    rw [hlbdef, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i (fun _ => c - μ i),
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_neg_distrib]
    simp only [Finset.mem_univ, if_pos]
    ring
  have hsum : (c - μ i) - ∑ j ∈ B, μ j ≤ ∑ j, (Rr j - μ j) := by
    rw [← hsumlb]; exact Finset.sum_le_sum fun j _ => hlb j
  have hS1 : (1 : ℝ) ≤ S₀ := one_le_sum_norm_sq_dadeCoverComplement hDade hinj hSIrr hν i
  have hstep : (c - μ i) - ∑ j ∈ B, μ j ≤ (N - S₀) / (Nat.card G : ℝ) := by
    have h1 : (S₀ - N) / (Nat.card G : ℝ) + ((c - μ i) - ∑ j ∈ B, μ j) ≤ 0 := by linarith
    have h2 : (N - S₀) / (Nat.card G : ℝ) = -((S₀ - N) / (Nat.card G : ℝ)) := by ring
    rw [h2]; linarith
  refine le_trans hstep ?_
  rw [div_le_div_iff_of_pos_right hGpos]
  linarith

end Main

end MultipleCoverDeficit

end CFSG.FeitThompson
