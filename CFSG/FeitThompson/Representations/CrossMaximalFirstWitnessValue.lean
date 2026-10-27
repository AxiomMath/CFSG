module

public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
public import CFSG.FeitThompson.Representations.ProjectionCoefficientsDistinctFamilies
public import CFSG.FeitThompson.Definitions.DadeAveragingMap
public import CFSG.FeitThompson.Representations.BlockDifferencesSupportedOutsideCore
import CFSG.FeitThompson.Representations.LargeKernelDadeInverseRecovery
import CFSG.FeitThompson.Representations.DadeBlockOrthogonalityCosetConstant
import CFSG.FeitThompson.Representations.OddNormalInducedBlocksConjPairs
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.CoherentNormalIrreducibleConjugation
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate ComplexOrder

open CrossFamilyProjection (coherentImage coherentImage_apply)

variable {G : Type*} [Group G] {L : Subgroup G}

theorem nonprincipalIrr_eq_sdiff_singleton (X : Type*) [Group X] :
    nonprincipalIrr X = Irr X \ {1} := by
  ext χ
  rw [mem_nonprincipalIrr, Set.mem_sdiff, Set.mem_singleton_iff]

theorem IsDadeData.of_subset [Finite G] {A B : Set G} {J : G → Subgroup G}
    (hD : IsDadeData L A J) (hBA : B ⊆ A)
    (hconj : ∀ ⦃a : G⦄, a ∈ B → ∀ ⦃x : G⦄, x ∈ L → x * a * x⁻¹ ∈ B) :
    IsDadeData L B J where
  subset_sdiff := hBA.trans hD.subset_sdiff
  conj_mem := hconj
  fusion := by intro a ha b hb; exact hD.fusion (hBA ha) (hBA hb)
  le_centralizer := by intro a ha; exact hD.le_centralizer (hBA ha)
  normal_subgroupOf := by intro a ha; exact hD.normal_subgroupOf (hBA ha)
  inf_eq_bot := by intro a ha; exact hD.inf_eq_bot (hBA ha)
  mul_eq := by intro a ha; exact hD.mul_eq (hBA ha)
  coprime_card := by intro a ha b hb; exact hD.coprime_card (hBA ha) (hBA hb)

theorem ambientPuncturedCore_eq_image [Finite G] {A : Set G} {H : Subgroup ↥L}
    {J : G → Subgroup G} (hD : IsDadeData L A J) (hA : A = ambientCoreCentralizerSupport H) :
    ambientPuncturedCore (G := G) H = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}) := by
  have hsub : ambientPuncturedCore (G := G) H ⊆ (L : Set G) := fun g hg =>
    hD.subset (by rw [hA]; exact ambientPuncturedCore_subset H hg)
  ext g
  refine ⟨fun hg => ?_, ?_⟩
  · have hgL : g ∈ L := hsub hg
    obtain ⟨hmem, hne⟩ := (mem_ambientPuncturedCore (G := G) (H := H) (x := ⟨g, hgL⟩)).1 hg
    exact ⟨⟨g, hgL⟩, ⟨hmem, by simpa using hne⟩, rfl⟩
  · rintro ⟨y, ⟨hyH, hy1⟩, rfl⟩
    exact mem_ambientPuncturedCore.2 ⟨hyH, by simpa using hy1⟩

theorem isDadeData_ambientPuncturedCore [Finite G] {A : Set G} {H : Subgroup ↥L} [H.Normal]
    {J : G → Subgroup G} (hD : IsDadeData L A J) (hA : A = ambientCoreCentralizerSupport H) :
    IsDadeData L (ambientPuncturedCore H) J := by
  refine hD.of_subset (hA ▸ ambientPuncturedCore_subset H) ?_
  intro a ha x hx
  rw [ambientPuncturedCore_eq_image hD hA] at ha ⊢
  obtain ⟨y, ⟨hyH, hy1⟩, rfl⟩ := ha
  refine ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹, ⟨‹H.Normal›.conj_mem y hyH ⟨x, hx⟩, ?_⟩, by simp⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  refine hy1 ?_
  have hy : y = 1 := by
    have h1 : (⟨x, hx⟩ : ↥L) * y * (⟨x, hx⟩ : ↥L)⁻¹ = 1 := hc
    simpa using h1
  simpa using hy

theorem dadeMapFun_eq_of_subset [Finite G] {A B : Set G} {J : G → Subgroup G}
    (hD : IsDadeData L A J) (hD' : IsDadeData L B J) (hBA : B ⊆ A)
    {f : ↥L → ℂ} (hf : f ∈ dadeDomain L B) :
    dadeMapFun L A J f = dadeMapFun L B J f := by
  funext x
  by_cases hxB : x ∈ totalDadeSupport B J
  · obtain ⟨b, hb, hxb⟩ := mem_totalDadeSupport_iff.1 hxB
    rw [← coe_dadeMap hD ⟨f, dadeDomain_mono hBA hf⟩,
      dadeMap_apply_of_mem_dadeSupport hD _ (hBA hb) hxb,
      ← coe_dadeMap hD' ⟨f, hf⟩, dadeMap_apply_of_mem_dadeSupport hD' _ hb hxb]
  · rw [dadeMapFun_eq_zero_of_notMem_totalDadeSupport hD (dadeDomain_mono hBA hf)
      (fun z hz => (mem_dadeDomain.1 hf).2 z hz) hxB, dadeMapFun_eq_zero_of_notMem L B J hxB]

section Block

variable [Fintype G] [Fintype ↥L] {H : Subgroup ↥L} [H.Normal] {J : G → Subgroup G}
  {ι : Type*} {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

omit [Fintype G] in
theorem self_mem_irrConstituents_of_mem_Irr {χ : ↥L → ℂ} (hχ : χ ∈ Irr ↥L) :
    χ ∈ irrConstituents χ :=
  mem_irrConstituents.2 ⟨hχ, by rw [cfInner_self_of_mem_Irr hχ]; exact zero_lt_one⟩

omit [Fintype G] [H.Normal] in
theorem mem_indFam_nonprincipalIrr_of_range_eq (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (k : ι) : ξ k ∈ indFam H (nonprincipalIrr ↥H) := by
  rw [nonprincipalIrr_eq_sdiff_singleton, ← hS]
  exact Set.mem_range_self k

omit [Fintype G] in
theorem mem_irrDetect_of_range_eq (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (hζIrr : ξ k₀ ∈ Irr ↥L) : ξ k₀ ∈ irrDetect ℂ H :=
  irrConstituents_subset_irrDetect H (mem_indFam_nonprincipalIrr_of_range_eq hS k₀)
    (self_mem_irrConstituents_of_mem_Irr hζIrr)

omit [Fintype G] [Fintype ↥L] in
theorem coherentImage_mem_classFun : coherentImage ξ ν k₀ ∈ classFun G := by
  rw [coherentImage_apply]
  exact virtualChars_le_classFun (ν _).2

theorem cfInner_self_coherentImage (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hζIrr : ξ k₀ ∈ Irr ↥L) : cfInner (coherentImage ξ ν k₀) (coherentImage ξ ν k₀) = 1 := by
  rw [coherentImage_apply, hν.inner_eq]
  exact cfInner_self_of_mem_Irr hζIrr

theorem coherentImage_mem_signedIrr (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hζIrr : ξ k₀ ∈ Irr ↥L) : coherentImage ξ ν k₀ ∈ signedIrr G := by
  refine mem_signedIrr.2 (mem_Irr_or_neg_mem_Irr_of_mem_span_Irr_of_cfInner_self_eq_one ?_
    (cfInner_self_coherentImage hν hζIrr))
  rw [coherentImage_apply]
  exact mem_span_Irr_of_mem_virtualChars (ν _).2

omit [Fintype G] in
theorem sub_star_mem_dadeDomain (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ)) :
    ξ k₀ - star (ξ k₀) ∈ dadeDomain L (ambientCoreCentralizerSupport H) := by
  have hζcf : ξ k₀ ∈ classFun ↥L := Irr_subset_classFun hζIrr
  refine mem_dadeDomain.2 ⟨sub_mem hζcf (star_mem_classFun hζcf), fun y hy => ?_⟩
  by_cases hyH : y ∈ H
  · have hy1 : y = 1 := by
      by_contra hne
      exact hy (ambientPuncturedCore_subset H (mem_ambientPuncturedCore.2 ⟨hyH, hne⟩))
    simp only [hy1, Pi.sub_apply, Pi.star_apply, RCLike.star_def, hζ1, Complex.conj_natCast,
      sub_self]
  · have h0 : ξ k₀ y = 0 :=
      eq_zero_of_mem_indFam_of_notMem H (hS ▸ Set.mem_range_self k₀) hyH
    simp [h0]

theorem cfInner_dadeMapFun_sub_star_coherentImage (hodd : Odd (Nat.card ↥L))
    (hD : IsDadeData L (ambientCoreCentralizerSupport H) J)
    (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L (ambientCoreCentralizerSupport H)),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ)) :
    cfInner (dadeMapFun L (ambientCoreCentralizerSupport H) J (ξ k₀ - star (ξ k₀)))
      (coherentImage ξ ν k₀) = 1 := by
  have hζS : ξ k₀ ∈ Set.range ξ := Set.mem_range_self k₀
  have hstarS : star (ξ k₀) ∈ Set.range ξ :=
    NormalInducedFamily.star_mem_of_mem (H := H) hS hζS
  have hstarIrr : star (ξ k₀) ∈ Irr ↥L := star_mem_Irr hζIrr
  have hne : star (ξ k₀) ≠ ξ k₀ := fun hc =>
    ne_conj_of_mem_indFam_nonprincipalIrr hodd H
      (θ := ξ k₀) (mem_indFam_nonprincipalIrr_of_range_eq hS k₀) hc.symm
  set g : Submodule.span ℤ (Set.range ξ) :=
    ⟨ξ k₀ - star (ξ k₀), sub_mem (Submodule.subset_span hζS) (Submodule.subset_span hstarS)⟩ with hg
  have hg1 : (g : ↥L → ℂ) 1 = 0 := by
    change (ξ k₀ - star (ξ k₀)) 1 = 0
    simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def, hζ1, Complex.conj_natCast, sub_self]
  set f₀ : charSpanZero (Set.range ξ) := ⟨(g : ↥L → ℂ), mem_charSpanZero.2 ⟨g.2, hg1⟩⟩ with hf₀
  have hincl : Submodule.inclusion (charSpanZero_le (Set.range ξ)) f₀ = g := Subtype.ext rfl
  have hνg : (ν g : G → ℂ) = (τ f₀ : G → ℂ) := by rw [← hincl, hν.eq_on_zero f₀]
  have hτF : (τ f₀ : G → ℂ) = dadeMapFun L (ambientCoreCentralizerSupport H) J
      (ξ k₀ - star (ξ k₀)) := by
    rw [hτ f₀ ⟨ξ k₀ - star (ξ k₀), sub_star_mem_dadeDomain hS hζIrr hζ1⟩ rfl, coe_dadeMap hD]
  rw [← hτF, ← hνg, coherentImage_apply]
  have hueq : (ν ⟨ξ k₀, Submodule.subset_span hζS⟩ : G → ℂ)
      = (ν ⟨ξ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩ : G → ℂ) := rfl
  rw [← hueq, hν.inner_eq g ⟨ξ k₀, Submodule.subset_span hζS⟩]
  change cfInner (ξ k₀ - star (ξ k₀)) (ξ k₀) = 1
  rw [cfInner_sub_left, cfInner_self_of_mem_Irr hζIrr,
    cfInner_eq_ite_of_mem_Irr hstarIrr hζIrr, if_neg hne, sub_zero]

theorem coherentImage_mem_signedRootBlock (hodd : Odd (Nat.card ↥L))
    (hD : IsDadeData L (ambientCoreCentralizerSupport H) J)
    (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L (ambientCoreCentralizerSupport H)),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ)) :
    coherentImage ξ ν k₀
      ∈ signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) (ξ k₀) := by
  obtain ⟨hηIrr, hηne, hηeq⟩ :=
    dadeRoot_spec (H := H) hD hodd rfl (mem_irrDetect_of_range_eq hS hζIrr)
  set η := dadeRoot L (ambientCoreCentralizerSupport H) J (ξ k₀) with hη
  have hstarIrr : star η ∈ Irr G := star_mem_Irr hηIrr
  have horth : cfInner η (star η) = 0 := by
    rw [cfInner_eq_ite_of_mem_Irr hηIrr hstarIrr, if_neg (fun hc => hηne hc.symm)]
  have hsub : cfInner (η - star η) (coherentImage ξ ν k₀) = 1 := by
    rw [← hηeq]
    exact cfInner_dadeMapFun_sub_star_coherentImage hodd hD hS hν hτ hζIrr hζ1
  exact signedPair_subset_signedRootBlock _ (self_mem_irrConstituents_of_mem_Irr hζIrr)
    (mem_signedPair.2 (eq_or_eq_neg_of_cfInner_sub_eq_one (Irr_subset_signedIrr hηIrr)
      (Irr_subset_signedIrr hstarIrr) (coherentImage_mem_signedIrr hν hζIrr) horth hsub))

omit [Fintype ↥L] in
theorem eq_dadeMap_ambientPuncturedCore
    (hD : IsDadeData L (ambientCoreCentralizerSupport H) J)
    (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L (ambientCoreCentralizerSupport H)),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (f : charSpanZero (Set.range ξ)) (F : dadeDomain L (ambientPuncturedCore H))
    (hfF : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    (τ f : G → ℂ)
      = ((dadeMap (isDadeData_ambientPuncturedCore hD rfl) F : classFun G) : G → ℂ) := by
  have hBA : ambientPuncturedCore (G := G) H ⊆ ambientCoreCentralizerSupport H :=
    ambientPuncturedCore_subset H
  have hD' := isDadeData_ambientPuncturedCore (H := H) hD rfl
  rw [hτ f ⟨(F : ↥L → ℂ), dadeDomain_mono hBA F.2⟩ hfF, coe_dadeMap hD, coe_dadeMap hD' F]
  exact dadeMapFun_eq_of_subset hD hD' hBA F.2

theorem dadeAverage_ambientPuncturedCore_coherentImage_eq [Finite ι]
    (hD : IsDadeData L (ambientCoreCentralizerSupport H) J)
    (hS : Set.range ξ = indFam H (Irr ↥H \ {1})) (hinj : Function.Injective ξ)
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L (ambientCoreCentralizerSupport H)),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ))
    (hS2 : (Set.range ξ).Nontrivial)
    {p : ℤ} (hp : 3 ≤ p) (hh : p ^ 2 ≤ (Nat.card ↥H : ℤ))
    (hep : 2 * (H.index : ℤ) ≤ p + 1)
    {x : ↥L} (hxH : x ∈ H) (hx1 : x ≠ 1) :
    dadeAverage (ambientPuncturedCore H) J (coherentImage ξ ν k₀) (x : G) = ξ k₀ x :=
  (NormalInducedFamily.dadeInverseRecovery_spec (isDadeData_ambientPuncturedCore hD rfl)
    (ambientPuncturedCore_eq_image hD rfl) hS hinj hν
    (eq_dadeMap_ambientPuncturedCore hD hτ) hζIrr hζ1 hS2 hp hh hep).2.2 x hxH hx1

end Block

section Main

variable {G : Type*} [Group G] [Fintype G] {L₁ L₂ : Subgroup G} [Fintype ↥L₁] [Fintype ↥L₂]
  {H₁ U₁ V₁ : Subgroup ↥L₁} [H₁.Normal] {H₂ U₂ V₂ : Subgroup ↥L₂} [H₂.Normal]
  {J₁ J₂ : G → Subgroup G} {ι : Type*} [Finite ι] {ξ : ι → (↥L₁ → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

theorem dadeAverage_eq_self_of_le_map
    (hD₁ : IsDadeData L₁ (ambientCoreCentralizerSupport H₁) J₁)
    (hconst : ∀ y : ↥L₂, y ∉ H₂ → ∀ u : ↥L₂, u ∈ H₂ →
      coherentImage ξ ν k₀ ((y : G) * (u : G)) = coherentImage ξ ν k₀ (y : G))
    {x₁ : ↥L₁} (hxH₁ : x₁ ∈ H₁) (hx1 : x₁ ≠ 1)
    {x₂ : ↥L₂} (hx₂ : (x₂ : G) = (x₁ : G)) (hxH₂ : x₂ ∉ H₂)
    (hJ : J₁ ((x₁ : ↥L₁) : G) ≤ H₂.map L₂.subtype) :
    dadeAverage (ambientPuncturedCore H₁) J₁ (coherentImage ξ ν k₀) ((x₁ : ↥L₁) : G)
      = coherentImage ξ ν k₀ ((x₁ : ↥L₁) : G) := by
  have hxA : ((x₁ : ↥L₁) : G) ∈ ambientPuncturedCore (G := G) H₁ :=
    mem_ambientPuncturedCore.2 ⟨hxH₁, hx1⟩
  refine dadeAverage_apply_of_eq_on hxA fun u hu => ?_
  have hcent : u * ((x₁ : ↥L₁) : G) = ((x₁ : ↥L₁) : G) * u :=
    (hD₁.le_centralizer (ambientPuncturedCore_subset H₁ hxA) hu _ rfl).symm
  obtain ⟨v, hv, hvu⟩ := (Subgroup.mem_map).1 (hJ hu)
  have hvu' : (v : G) = u := hvu
  calc coherentImage ξ ν k₀ (u * ((x₁ : ↥L₁) : G))
      = coherentImage ξ ν k₀ ((x₂ : G) * (v : G)) := by rw [hcent, hx₂, hvu']
    _ = coherentImage ξ ν k₀ (x₂ : G) := hconst x₂ hxH₂ v hv
    _ = coherentImage ξ ν k₀ ((x₁ : ↥L₁) : G) := by rw [hx₂]

theorem apply_mul_eq_of_cross_maximal
    (h₁ : IsFTTypeOneLocalSetup L₁ H₁ U₁ V₁ J₁) (h₂ : IsFTTypeOneLocalSetup L₂ H₂ U₂ V₂ J₂)
    (hsep : Disjoint (totalDadeSupport (ambientPuncturedCore H₁) J₁)
          (totalDadeSupport (ambientCoreCentralizerSupport H₂) J₂) ∨
        Disjoint (totalDadeSupport (ambientPuncturedCore H₂) J₂)
          (totalDadeSupport (ambientCoreCentralizerSupport H₁) J₁))
    (hstab : (Subtype.val '' coreCentralizerSupportOutsideCore H₂ : Set G).Nonempty →
      ∀ g : G, (fun y => g⁻¹ * y * g) '' (Subtype.val '' coreCentralizerSupportOutsideCore H₂)
        = Subtype.val '' coreCentralizerSupportOutsideCore H₂ ↔ g ∈ L₂)
    (hdisjQ : (Subtype.val '' coreCentralizerSupportOutsideCore H₂ : Set G).Nonempty →
      ∀ g ∉ L₂, (Subtype.val '' coreCentralizerSupportOutsideCore H₂ : Set G) ∩
        (fun y => g⁻¹ * y * g) '' (Subtype.val '' coreCentralizerSupportOutsideCore H₂) = ∅)
    (hS : Set.range ξ = indFam H₁ (Irr ↥H₁ \ {1})) (hinj : Function.Injective ξ)
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hτ : ∀ (f : charSpanZero (Set.range ξ))
        (F : dadeDomain L₁ (ambientCoreCentralizerSupport H₁)),
      (f : ↥L₁ → ℂ) = (F : ↥L₁ → ℂ) →
        (τ f : G → ℂ) = ((dadeMap h₁.dadeData F : classFun G) : G → ℂ))
    (hζIrr : ξ k₀ ∈ Irr ↥L₁) (hζ1 : ξ k₀ 1 = (H₁.index : ℂ))
    (hS2 : (Set.range ξ).Nontrivial)
    {p : ℤ} (hp : 3 ≤ p) (hh : p ^ 2 ≤ (Nat.card ↥H₁ : ℤ))
    (hep : 2 * (H₁.index : ℤ) ≤ p + 1)
    {x₁ : ↥L₁} (hxH₁ : x₁ ∈ H₁) (hx1 : x₁ ≠ 1)
    {x₂ : ↥L₂} (hx₂ : (x₂ : G) = (x₁ : G)) (hxH₂ : x₂ ∉ H₂)
    (hJ : J₁ ((x₁ : ↥L₁) : G) ≤ H₂.map L₂.subtype)
    {h : ↥L₂} (hh₂ : h ∈ H₂) :
    coherentImage ξ ν k₀ (((x₁ : ↥L₁) : G) * (h : G)) = ξ k₀ x₁ := by
  have hΨblock : coherentImage ξ ν k₀
      ∈ signedRootBlock (dadeRoot L₁ (ambientCoreCentralizerSupport H₁) J₁) (ξ k₀) :=
    coherentImage_mem_signedRootBlock h₁.odd_natCard h₁.dadeData hS hν hτ hζIrr hζ1
  have horth : ∀ θ ∈ indFam H₂ (nonprincipalIrr ↥H₂),
      ∀ ρ ∈ signedRootBlock (dadeRoot L₂ (ambientCoreCentralizerSupport H₂) J₂) θ,
        IsOrthogonal (coherentImage ξ ν k₀) ρ := fun θ hθ ρ hρ =>
    isOrthogonal_of_disjoint_oriented h₁ h₂
      (mem_indFam_nonprincipalIrr_of_range_eq hS k₀) hθ hsep _ hΨblock _ hρ
  have hconst : ∀ y : ↥L₂, y ∉ H₂ → ∀ u : ↥L₂, u ∈ H₂ →
      coherentImage ξ ν k₀ ((y : G) * (u : G)) = coherentImage ξ ν k₀ (y : G) := fun y hy u hu =>
    apply_mul_eq_of_isOrthogonal_signedRootBlock_dadeRoot h₂.dadeData h₂.frobeniusType
      h₂.odd_natCard rfl rfl hstab hdisjQ coherentImage_mem_classFun horth hy hu
  have hrec : dadeAverage (ambientPuncturedCore H₁) J₁ (coherentImage ξ ν k₀)
      ((x₁ : ↥L₁) : G) = ξ k₀ x₁ :=
    dadeAverage_ambientPuncturedCore_coherentImage_eq h₁.dadeData hS hinj hν hτ hζIrr hζ1 hS2
      hp hh hep hxH₁ hx1
  have hval : coherentImage ξ ν k₀ ((x₁ : ↥L₁) : G) = ξ k₀ x₁ := by
    rw [← hrec, dadeAverage_eq_self_of_le_map h₁.dadeData hconst hxH₁ hx1 hx₂ hxH₂ hJ]
  rw [← hx₂, hconst x₂ hxH₂ h hh₂, hx₂, hval]

theorem apply_eq_of_cross_maximal
    (h₁ : IsFTTypeOneLocalSetup L₁ H₁ U₁ V₁ J₁) (h₂ : IsFTTypeOneLocalSetup L₂ H₂ U₂ V₂ J₂)
    (hsep : Disjoint (totalDadeSupport (ambientPuncturedCore H₁) J₁)
          (totalDadeSupport (ambientCoreCentralizerSupport H₂) J₂) ∨
        Disjoint (totalDadeSupport (ambientPuncturedCore H₂) J₂)
          (totalDadeSupport (ambientCoreCentralizerSupport H₁) J₁))
    (hstab : (Subtype.val '' coreCentralizerSupportOutsideCore H₂ : Set G).Nonempty →
      ∀ g : G, (fun y => g⁻¹ * y * g) '' (Subtype.val '' coreCentralizerSupportOutsideCore H₂)
        = Subtype.val '' coreCentralizerSupportOutsideCore H₂ ↔ g ∈ L₂)
    (hdisjQ : (Subtype.val '' coreCentralizerSupportOutsideCore H₂ : Set G).Nonempty →
      ∀ g ∉ L₂, (Subtype.val '' coreCentralizerSupportOutsideCore H₂ : Set G) ∩
        (fun y => g⁻¹ * y * g) '' (Subtype.val '' coreCentralizerSupportOutsideCore H₂) = ∅)
    (hS : Set.range ξ = indFam H₁ (Irr ↥H₁ \ {1})) (hinj : Function.Injective ξ)
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hτ : ∀ (f : charSpanZero (Set.range ξ))
        (F : dadeDomain L₁ (ambientCoreCentralizerSupport H₁)),
      (f : ↥L₁ → ℂ) = (F : ↥L₁ → ℂ) →
        (τ f : G → ℂ) = ((dadeMap h₁.dadeData F : classFun G) : G → ℂ))
    (hζIrr : ξ k₀ ∈ Irr ↥L₁) (hζ1 : ξ k₀ 1 = (H₁.index : ℂ))
    (hS2 : (Set.range ξ).Nontrivial)
    {p : ℤ} (hp : 3 ≤ p) (hh : p ^ 2 ≤ (Nat.card ↥H₁ : ℤ))
    (hep : 2 * (H₁.index : ℤ) ≤ p + 1)
    {x₁ : ↥L₁} (hxH₁ : x₁ ∈ H₁) (hx1 : x₁ ≠ 1)
    {x₂ : ↥L₂} (hx₂ : (x₂ : G) = (x₁ : G)) (hxH₂ : x₂ ∉ H₂)
    (hJ : J₁ ((x₁ : ↥L₁) : G) ≤ H₂.map L₂.subtype) :
    coherentImage ξ ν k₀ ((x₁ : ↥L₁) : G) = ξ k₀ x₁ := by
  have key := apply_mul_eq_of_cross_maximal h₁ h₂ hsep hstab hdisjQ hS hinj hν hτ hζIrr hζ1 hS2
    hp hh hep hxH₁ hx1 hx₂ hxH₂ hJ (h := (1 : ↥L₂)) (Subgroup.one_mem H₂)
  simpa using key

end Main

end CFSG.FeitThompson
