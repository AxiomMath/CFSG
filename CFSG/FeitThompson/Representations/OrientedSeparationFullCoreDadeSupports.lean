module

public import CFSG.FeitThompson.Representations.FrobeniusTypeLocalBlockData
public import CFSG.FeitThompson.Representations.SignedPairInducedBlockSpans
public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.EqualDegreeBlocksImagesSupportedPairs
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

noncomputable section

variable {G : Type*} [Group G] {L : Subgroup G}

theorem eq_zero_of_mem_span_of_forall_eq_zero {α : Type*} {S : Set (α → ℂ)} {x : α}
    (hS : ∀ s ∈ S, s x = 0) {f : α → ℂ} (hf : f ∈ Submodule.span ℤ S) : f x = 0 := by
  have h : Submodule.span ℤ S ≤ LinearMap.ker (LinearMap.proj x : (α → ℂ) →ₗ[ℤ] ℂ) := by
    rw [Submodule.span_le]
    intro g hg
    simpa using hS g hg
  simpa using h hf

def dadeMapFun (L : Subgroup G) (A : Set G) (J : G → Subgroup G) (f : ↥L → ℂ) : G → ℂ :=
  dadeSupportExtension A J (extendByZero L f)

theorem dadeMapFun_def (L : Subgroup G) (A : Set G) (J : G → Subgroup G) (f : ↥L → ℂ) :
    dadeMapFun L A J f = dadeSupportExtension A J (extendByZero L f) := (rfl)

section MapFun

variable (L) (A : Set G) (J : G → Subgroup G)

theorem dadeMapFun_add (f g : ↥L → ℂ) :
    dadeMapFun L A J (f + g) = dadeMapFun L A J f + dadeMapFun L A J g := by
  rw [dadeMapFun, dadeMapFun, dadeMapFun, extendByZero_add, dadeSupportExtension_add]

theorem dadeMapFun_smul (c : ℂ) (f : ↥L → ℂ) :
    dadeMapFun L A J (c • f) = c • dadeMapFun L A J f := by
  rw [dadeMapFun, dadeMapFun, extendByZero_smul, dadeSupportExtension_smul]

theorem dadeMapFun_neg (f : ↥L → ℂ) : dadeMapFun L A J (-f) = -dadeMapFun L A J f := by
  simpa using dadeMapFun_smul L A J (-1) f

theorem dadeMapFun_star (f : ↥L → ℂ) :
    dadeMapFun L A J (star f) = star (dadeMapFun L A J f) := by
  rw [dadeMapFun, dadeMapFun, extendByZero_star, dadeSupportExtension_star]

theorem dadeMapFun_eq_zero_of_notMem {f : ↥L → ℂ} {x : G} (hx : x ∉ totalDadeSupport A J) :
    dadeMapFun L A J f x = 0 :=
  dadeSupportExtension_eq_zero_of_notMem hx

theorem support_dadeMapFun_subset (f : ↥L → ℂ) :
    Function.support (dadeMapFun L A J f) ⊆ totalDadeSupport A J :=
  support_dadeSupportExtension_subset

theorem star_dadeMapFun_sub_star (f : ↥L → ℂ) :
    star (dadeMapFun L A J (f - star f)) = -dadeMapFun L A J (f - star f) := by
  rw [← dadeMapFun_star, star_sub, star_star, show star f - f = -(f - star f) by ring,
    dadeMapFun_neg]

end MapFun

theorem coe_dadeMap [Finite G] {A : Set G} {J : G → Subgroup G} (hD : IsDadeData L A J)
    (f : dadeDomain L A) :
    ((dadeMap hD f : classFun G) : G → ℂ) = dadeMapFun L A J (f : ↥L → ℂ) :=
  dadeMap_apply_coe hD f

theorem dadeMapFun_eq_zero_of_notMem_totalDadeSupport [Finite G] {A B : Set G}
    {J : G → Subgroup G} (hD : IsDadeData L A J) {f : ↥L → ℂ} (hf : f ∈ dadeDomain L A)
    (hf0 : ∀ x : ↥L, (x : G) ∉ B → f x = 0) {x : G} (hx : x ∉ totalDadeSupport B J) :
    dadeMapFun L A J f x = 0 := by
  by_cases hxA : x ∈ totalDadeSupport A J
  · obtain ⟨a, ha, hxa⟩ := mem_totalDadeSupport_iff.1 hxA
    rw [← coe_dadeMap hD ⟨f, hf⟩, dadeMap_apply_of_mem_dadeSupport hD ⟨f, hf⟩ ha hxa]
    exact hf0 _ fun hB => hx (mem_totalDadeSupport_iff.2 ⟨a, hB, hxa⟩)
  · exact dadeMapFun_eq_zero_of_notMem L A J hxA

def dadeRoot (L : Subgroup G) (A : Set G) (J : G → Subgroup G) (χ : ↥L → ℂ) : G → ℂ :=
  antirealRoot (dadeMapFun L A J (χ - star χ))

theorem dadeRoot_def (L : Subgroup G) (A : Set G) (J : G → Subgroup G) (χ : ↥L → ℂ) :
    dadeRoot L A J χ = antirealRoot (dadeMapFun L A J (χ - star χ)) := (rfl)

def ambientCoreCentralizerSupport (H : Subgroup ↥L) : Set G :=
  (fun x : ↥L => (x : G)) '' coreCentralizerSupport H

def ambientPuncturedCore (H : Subgroup ↥L) : Set G :=
  (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1})

theorem ambientPuncturedCore_eq_image_sdiff (H : Subgroup ↥L) :
    ambientPuncturedCore (G := G) H = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}) := (rfl)

theorem ambientPuncturedCore_subset_coe (H : Subgroup ↥L) :
    ambientPuncturedCore (G := G) H ⊆ (L : Set G) := by
  rw [ambientPuncturedCore_eq_image_sdiff]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_ambientCoreCentralizerSupport {H : Subgroup ↥L} {x : ↥L} :
    (x : G) ∈ ambientCoreCentralizerSupport H ↔ x ∈ coreCentralizerSupport H := by
  simp only [ambientCoreCentralizerSupport, Set.mem_image]
  exact ⟨fun ⟨y, hy, hxy⟩ => by rwa [Subtype.coe_injective hxy] at hy, fun h => ⟨x, h, rfl⟩⟩

theorem ambientCoreCentralizerSupport_eq_image (H : Subgroup ↥L) :
    ambientCoreCentralizerSupport (G := G) H
      = (fun x : ↥L => (x : G)) '' coreCentralizerSupport H := (rfl)

theorem ambientCoreCentralizerSupport_subset_coe (H : Subgroup ↥L) :
    ambientCoreCentralizerSupport (G := G) H ⊆ (L : Set G) := by
  rw [ambientCoreCentralizerSupport_eq_image]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_ambientPuncturedCore {H : Subgroup ↥L} {x : ↥L} :
    (x : G) ∈ ambientPuncturedCore H ↔ x ∈ H ∧ x ≠ 1 := by
  simp only [ambientPuncturedCore, Set.mem_image, Set.mem_sdiff, SetLike.mem_coe,
    Set.mem_singleton_iff]
  exact ⟨fun ⟨y, hy, hxy⟩ => by rwa [Subtype.coe_injective hxy] at hy, fun h => ⟨x, h, rfl⟩⟩

theorem ambientPuncturedCore_subset (H : Subgroup ↥L) :
    ambientPuncturedCore (G := G) H ⊆ ambientCoreCentralizerSupport H := by
  rintro _ ⟨x, ⟨hxH, hx1⟩, rfl⟩
  have hx1' : x ≠ 1 := by simpa using hx1
  refine mem_ambientCoreCentralizerSupport.2 (mem_coreCentralizerSupport.2 ⟨hx1', ?_⟩)
  intro hbot
  have hmem : x ∈ H ⊓ Subgroup.centralizer ({x} : Set ↥L) :=
    ⟨hxH, Subgroup.mem_centralizer_iff.2 (by simp)⟩
  rw [hbot] at hmem
  exact hx1' (by simpa using hmem)

theorem totalDadeSupport_ambientPuncturedCore_subset (H : Subgroup ↥L) (J : G → Subgroup G) :
    totalDadeSupport (ambientPuncturedCore H) J
      ⊆ totalDadeSupport (ambientCoreCentralizerSupport H) J := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := mem_totalDadeSupport_iff.1 hx
  exact mem_totalDadeSupport_iff.2 ⟨a, ambientPuncturedCore_subset H ha, hxa⟩

theorem mem_dadeDomain_of_mem_charSpanZero_irrDetect [Finite G] [Finite ↥L]
    {H : Subgroup ↥L} [H.Normal] {f : ↥L → ℂ} (hf : f ∈ charSpanZero (irrDetect ℂ H)) :
    f ∈ dadeDomain L (ambientCoreCentralizerSupport H) := by
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeDomain_of_mem_span_Irr (Submodule.span_mono (irrDetect_subset_Irr H) hspan) ?_
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; exact h1
  · refine eq_zero_of_mem_span_of_forall_eq_zero (fun χ hχ => ?_) hspan
    refine eq_zero_of_notMem_insert_one_coreCentralizerSupport hχ ?_
    simp only [Set.mem_insert_iff]
    push Not
    exact ⟨hx1, fun h => hx (mem_ambientCoreCentralizerSupport.2 h)⟩

theorem isAntirealIsometry_dadeMapFun [Fintype G] [Fintype ↥L] {H : Subgroup ↥L} [H.Normal]
    {J : G → Subgroup G} (hodd : Odd (Nat.card ↥L))
    (hD : IsDadeData L (ambientCoreCentralizerSupport H) J) :
    IsAntirealIsometry (irrDetect ℂ H) (dadeMapFun L (ambientCoreCentralizerSupport H) J) := by
  set A := ambientCoreCentralizerSupport (L := L) H with hA
  refine isAntirealIsometry_irrDetect hodd H
    (fun f _ g _ => dadeMapFun_add L A J f g) (fun f hf => ?_) (fun f hf g hg => ?_)
    (fun f _ => dadeMapFun_eq_zero_of_notMem L A J hD.one_notMem_totalDadeSupport)
    (fun f _ => dadeMapFun_star L A J f)
  · rw [← coe_dadeMap hD ⟨f, mem_dadeDomain_of_mem_charSpanZero_irrDetect hf⟩]
    exact hD.dadeMap_mem_span_Irr _
      (Submodule.span_mono (irrDetect_subset_Irr H) (mem_charSpanZero.1 hf).1)
  · rw [← coe_dadeMap hD ⟨f, mem_dadeDomain_of_mem_charSpanZero_irrDetect hf⟩,
      ← coe_dadeMap hD ⟨g, mem_dadeDomain_of_mem_charSpanZero_irrDetect hg⟩]
    exact cfInner_dadeMap hD _ _

structure IsFTTypeOneLocalSetup [Finite G] (L : Subgroup G) (H U V : Subgroup ↥L) [H.Normal]
    (J : G → Subgroup G) : Prop where
  odd_natCard : Odd (Nat.card ↥L)
  frobeniusType : IsFrobeniusTypeLocalData H U V
  dadeData : IsDadeData L (ambientCoreCentralizerSupport H) J

namespace IsFTTypeOneLocalSetup

section Root

variable [Finite G] [Finite ↥L] {H U V : Subgroup ↥L} [H.Normal] {J : G → Subgroup G}
  (h : IsFTTypeOneLocalSetup L H U V J)

include h

theorem existsUnique_dadeRoot {χ : ↥L → ℂ} (hχ : χ ∈ irrDetect ℂ H) :
    ∃! η : G → ℂ, η ∈ Irr G ∧ star η ≠ η ∧
      dadeMapFun L (ambientCoreCentralizerSupport H) J (χ - star χ) = η - star η := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥L := Fintype.ofFinite _
  exact (isAntirealIsometry_dadeMapFun h.odd_natCard h.dadeData).existsUnique_root hχ

theorem dadeRoot_spec {χ : ↥L → ℂ} (hχ : χ ∈ irrDetect ℂ H) :
    dadeRoot L (ambientCoreCentralizerSupport H) J χ ∈ Irr G ∧
      star (dadeRoot L (ambientCoreCentralizerSupport H) J χ)
          ≠ dadeRoot L (ambientCoreCentralizerSupport H) J χ ∧
      dadeMapFun L (ambientCoreCentralizerSupport H) J (χ - star χ)
        = dadeRoot L (ambientCoreCentralizerSupport H) J χ
          - star (dadeRoot L (ambientCoreCentralizerSupport H) J χ) := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype ↥L := Fintype.ofFinite _
  have hτ := isAntirealIsometry_dadeMapFun h.odd_natCard h.dadeData
  exact ⟨hτ.root_mem_Irr hχ, hτ.star_root_ne hχ, hτ.map_sub_star_eq hχ⟩

end Root

section Family

variable [Fintype G] [Fintype ↥L] {H U V : Subgroup ↥L} [H.Normal] {J : G → Subgroup G}
  (h : IsFTTypeOneLocalSetup L H U V J)

include h

theorem isAntirealIsometry :
    IsAntirealIsometry (irrDetect ℂ H) (dadeMapFun L (ambientCoreCentralizerSupport H) J) :=
  isAntirealIsometry_dadeMapFun h.odd_natCard h.dadeData

theorem isNormalInducedSignedFamily :
    IsNormalInducedSignedFamily H (dadeMapFun L (ambientCoreCentralizerSupport H) J)
      (dadeRoot L (ambientCoreCentralizerSupport H) J) := by
  have hτ := h.isAntirealIsometry
  have hsum : ∀ θ ∈ indFam H (nonprincipalIrr ↥H),
      θ = ∑ χ ∈ irrConstituentsFinset θ, χ := by
    intro θ hθ
    obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
    have hF : irrConstituentsFinset (indClassFun H lam)
        = (finite_irrConstituents (indClassFun H lam)).toFinset := by
      apply Finset.coe_injective
      rw [coe_irrConstituentsFinset, Set.Finite.coe_toFinset]
    rw [hF]
    exact indClassFun_eq_sum_irrConstituents h.frobeniusType hlam
  have hdeg : ∀ θ ∈ indFam H (nonprincipalIrr ↥H), ∀ χ ∈ irrConstituents θ,
      ∀ ψ ∈ irrConstituents θ, χ 1 = ψ 1 := by
    intro θ hθ χ hχ ψ hψ
    obtain ⟨lam, hlam, rfl⟩ := (mem_indFam H).1 hθ
    rw [apply_one_of_mem_irrConstituents h.frobeniusType hlam hχ,
      apply_one_of_mem_irrConstituents h.frobeniusType hlam hψ]
  exact { odd_natCard := h.odd_natCard
          ne_bot := h.frobeniusType.core_ne_bot
          isAntirealIsometry := hτ
          eq_sum_irrConstituents := hsum
          apply_one_eq := hdeg
          root_mem_Irr := fun χ hχ => hτ.root_mem_Irr hχ
          map_sub_star_eq := fun χ hχ => hτ.map_sub_star_eq hχ }

variable {θ : ↥L → ℂ} (hθ : θ ∈ indFam H (nonprincipalIrr ↥H))

include hθ

theorem cfInner_of_mem_signedRootBlock {ρ σ : G → ℂ}
    (hρ : ρ ∈ signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) θ)
    (hσ : σ ∈ signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) θ) :
    cfInner ρ σ = if ρ = σ then 1 else 0 :=
  h.isNormalInducedSignedFamily.cfInner_of_mem_signedRootBlock hθ hρ hσ

end Family

section Support

variable [Finite G] [Fintype ↥L] {H U V : Subgroup ↥L} [H.Normal] {J : G → Subgroup G}
  (h : IsFTTypeOneLocalSetup L H U V J) {θ : ↥L → ℂ}
  (hθ : θ ∈ indFam H (nonprincipalIrr ↥H))

include h hθ

theorem sub_star_mem_charSpanZero : θ - star θ ∈ charSpanZero (irrDetect ℂ H) := by
  have : Fintype G := Fintype.ofFinite G
  rw [h.isNormalInducedSignedFamily.sub_star_eq_sum hθ]
  exact Submodule.sum_mem _ fun χ hχ =>
    h.isAntirealIsometry.sub_star_mem
      (irrConstituents_subset_irrDetect H hθ (by simpa using hχ))

theorem sub_star_apply_eq_zero (x : ↥L) (hx : (x : G) ∉ ambientPuncturedCore H) :
    (θ - star θ) x = 0 := by
  by_cases hxH : x ∈ H
  · have hx1 : x = 1 := by
      by_contra hne
      exact hx (mem_ambientPuncturedCore.2 ⟨hxH, hne⟩)
    rw [hx1]
    exact (mem_charSpanZero.1 (h.sub_star_mem_charSpanZero hθ)).2
  · have h0 : θ x = 0 := eq_zero_of_mem_indFam_of_notMem H hθ hxH
    simp [h0]

theorem signedRootBlock_subset_signedIrr :
    (signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) θ : Set (G → ℂ))
      ⊆ signedIrr G := by
  have : Fintype G := Fintype.ofFinite G
  exact h.isNormalInducedSignedFamily.signedRootBlock_subset_signedIrr hθ

theorem sum_signedRootBlock_apply_eq_zero_of_notMem
    {x : G} (hx : x ∉ totalDadeSupport (ambientPuncturedCore H) J) :
    (∑ ρ ∈ signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) θ, ρ) x = 0 := by
  have : Fintype G := Fintype.ofFinite G
  rw [← h.isNormalInducedSignedFamily.sum_signedRootBlock hθ]
  exact dadeMapFun_eq_zero_of_notMem_totalDadeSupport h.dadeData
    (mem_dadeDomain_of_mem_charSpanZero_irrDetect (h.sub_star_mem_charSpanZero hθ))
    (h.sub_star_apply_eq_zero hθ) hx

theorem conj_sum_signedRootBlock (x : G) :
    conj ((∑ ρ ∈ signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) θ, ρ) x)
      = -((∑ ρ ∈ signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) θ, ρ) x) := by
  have : Fintype G := Fintype.ofFinite G
  rw [← h.isNormalInducedSignedFamily.sum_signedRootBlock hθ]
  simpa using congrFun (star_dadeMapFun_sub_star L (ambientCoreCentralizerSupport H) J θ) x

theorem sub_conj_apply_eq_zero_of_mem_signedRootBlock {a : G → ℂ}
    (ha : a ∈ signedRootBlock (dadeRoot L (ambientCoreCentralizerSupport H) J) θ)
    {x : G} (hx : x ∉ totalDadeSupport (ambientCoreCentralizerSupport H) J) :
    a x - conj (a x) = 0 := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨χ, hχ, ha'⟩ := (mem_signedRootBlock _ θ).1 ha
  have hkey : a - star a
      = dadeMapFun L (ambientCoreCentralizerSupport H) J (χ - star χ) := by
    rw [h.isNormalInducedSignedFamily.map_sub_star_eq_of_mem hθ hχ]
    rcases mem_signedPair.1 ha' with rfl | rfl
    · rfl
    · rw [star_neg, star_star]; ring
  have hval := congrFun hkey x
  simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def] at hval
  rw [hval, dadeMapFun_eq_zero_of_notMem L _ J hx]

end Support

end IsFTTypeOneLocalSetup

section Main

variable {G : Type*} [Group G] [Fintype G] {L₁ L₂ : Subgroup G} [Fintype ↥L₁] [Fintype ↥L₂]
  {H₁ U₁ V₁ : Subgroup ↥L₁} [H₁.Normal] {H₂ U₂ V₂ : Subgroup ↥L₂} [H₂.Normal]
  {J₁ J₂ : G → Subgroup G}
  (h₁ : IsFTTypeOneLocalSetup L₁ H₁ U₁ V₁ J₁) (h₂ : IsFTTypeOneLocalSetup L₂ H₂ U₂ V₂ J₂)
  {θ₁ : ↥L₁ → ℂ} {θ₂ : ↥L₂ → ℂ}
  (hθ₁ : θ₁ ∈ indFam H₁ (nonprincipalIrr ↥H₁)) (hθ₂ : θ₂ ∈ indFam H₂ (nonprincipalIrr ↥H₂))

include h₁ h₂ hθ₁ hθ₂

theorem cfInner_eq_zero_of_disjoint_core_full
    (hdisj : Disjoint (totalDadeSupport (ambientPuncturedCore H₂) J₂)
      (totalDadeSupport (ambientCoreCentralizerSupport H₁) J₁))
    {a b : G → ℂ}
    (ha : a ∈ signedRootBlock (dadeRoot L₁ (ambientCoreCentralizerSupport H₁) J₁) θ₁)
    (hb : b ∈ signedRootBlock (dadeRoot L₂ (ambientCoreCentralizerSupport H₂) J₂) θ₂) :
    cfInner a b = 0 :=
  cfInner_eq_zero_of_conj_eq_neg_of_disjoint_support
    (fun _ hx => h₁.signedRootBlock_subset_signedIrr hθ₁ (by simpa using hx))
    (fun _ hx => h₂.signedRootBlock_subset_signedIrr hθ₂ (by simpa using hx))
    (fun _ hx _ hy => h₂.cfInner_of_mem_signedRootBlock hθ₂ hx hy)
    hdisj.symm (h₂.conj_sum_signedRootBlock hθ₂)
    (fun _ hx => h₂.sum_signedRootBlock_apply_eq_zero_of_notMem hθ₂ hx)
    (fun _ hx _ hy => h₁.sub_conj_apply_eq_zero_of_mem_signedRootBlock hθ₁ hx hy) ha hb

theorem cfInner_eq_zero_of_disjoint_oriented
    (hdisj : Disjoint (totalDadeSupport (ambientPuncturedCore H₁) J₁)
        (totalDadeSupport (ambientCoreCentralizerSupport H₂) J₂) ∨
      Disjoint (totalDadeSupport (ambientPuncturedCore H₂) J₂)
        (totalDadeSupport (ambientCoreCentralizerSupport H₁) J₁))
    {a b : G → ℂ}
    (ha : a ∈ signedRootBlock (dadeRoot L₁ (ambientCoreCentralizerSupport H₁) J₁) θ₁)
    (hb : b ∈ signedRootBlock (dadeRoot L₂ (ambientCoreCentralizerSupport H₂) J₂) θ₂) :
    cfInner a b = 0 := by
  rcases hdisj with hd | hd
  · have h0 := cfInner_eq_zero_of_disjoint_core_full h₂ h₁ hθ₂ hθ₁ hd hb ha
    have hc := conj_cfInner b a
    rw [h0] at hc
    simpa using hc.symm
  · exact cfInner_eq_zero_of_disjoint_core_full h₁ h₂ hθ₁ hθ₂ hd ha hb

theorem isOrthogonal_of_disjoint_oriented
    (hdisj : Disjoint (totalDadeSupport (ambientPuncturedCore H₁) J₁)
        (totalDadeSupport (ambientCoreCentralizerSupport H₂) J₂) ∨
      Disjoint (totalDadeSupport (ambientPuncturedCore H₂) J₂)
        (totalDadeSupport (ambientCoreCentralizerSupport H₁) J₁)) :
    ∀ a ∈ signedRootBlock (dadeRoot L₁ (ambientCoreCentralizerSupport H₁) J₁) θ₁,
      ∀ b ∈ signedRootBlock (dadeRoot L₂ (ambientCoreCentralizerSupport H₂) J₂) θ₂,
        IsOrthogonal a b := fun _ ha _ hb =>
  isOrthogonal_iff.2 (cfInner_eq_zero_of_disjoint_oriented h₁ h₂ hθ₁ hθ₂ hdisj ha hb)

end Main

end

end CFSG.FeitThompson
