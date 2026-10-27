module

public import CFSG.FeitThompson.Representations.NonprincipalRowSumsCoreCentralizers
public import CFSG.FeitThompson.Representations.OddNormalInducedBlocksConjPairs
public import CFSG.FeitThompson.Representations.FreeCentralSectionCoherentLayer
public import CFSG.FeitThompson.Representations.DisjointSupportCoherentFamiliesOrthogonal
public import CFSG.FeitThompson.Representations.EqualDegreeBlocksImagesSupportedPairs
public import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.EqualDegreeDifferenceSaturatesAntirealBlocks
public import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars
public import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
public import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
public import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
public import CFSG.FeitThompson.Representations.CoreDetectingFamilyAntirealBlocksSupport
public import CFSG.FeitThompson.Representations.PrimeTIInvariantMovingEqualDegreeRow
public import CFSG.FeitThompson.Representations.SmallCharactersPerpendicularCyclicTIArray

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

namespace PrimeDadeSubcoherence

section Family

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {K : Subgroup ↥L}

omit [Fintype G] in
theorem indFamDetect_subset_indFam_Irr (K : Subgroup ↥L) (H : Subgroup ↥K) :
    indFamDetect K H ⊆ indFam K (Irr ↥K) := by
  rw [Irr_eq_irrChar]; exact indFamDetect_subset_indFam_irrChar K H

omit [Fintype G] in
theorem mem_span_Irr_of_mem_indFamDetect {H : Subgroup ↥K} {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect K H) : f ∈ Submodule.span ℤ (Irr ↥L) := by
  obtain ⟨W, rfl⟩ := NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam K
    (indFamDetect_subset_indFam_Irr K H hf)
  exact FDRep.character_mem_span_Irr W

omit [Fintype G] in
theorem isCharacter_of_mem_indFamDetect {H : Subgroup ↥K} {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect K H) : IsCharacter ↥L f :=
  isCharacter_iff.2 (NormalInducedFamily.exists_fdRep_character_eq_of_mem_indFam K
    (indFamDetect_subset_indFam_Irr K H hf))

omit [Fintype G] in
theorem ne_zero_of_mem_indFamDetect {H : Subgroup ↥K} {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect K H) : f ≠ 0 :=
  NormalInducedFamily.ne_zero_of_mem_indFam K (indFamDetect_subset_indFam_Irr K H hf)

omit [Fintype G] in
theorem star_mem_indFamDetect {H : Subgroup ↥K} {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect K H) : star f ∈ indFamDetect K H := by
  rw [indFamDetect_eq_indFam] at hf ⊢
  exact DisjointCoherentFamilies.star_mem_indFam K (fun _ hθ => star_mem_irrDetect hθ) hf

omit [Fintype G] in
theorem star_ne_self_of_mem_indFamDetect [K.Normal] (hodd : Odd (Nat.card ↥L))
    {H : Subgroup ↥K} {f : ↥L → ℂ} (hf : f ∈ indFamDetect K H) : star f ≠ f := by
  have h := ne_conj_of_mem_indFam_nonprincipalIrr hodd K
    (indFamDetect_subset_indFam_nonprincipalIrr K H hf)
  intro hc
  exact h (by simpa [funext_iff, Pi.star_apply, eq_comm] using hc)

omit [Fintype G] in
theorem cfInner_eq_zero_of_mem_indFamDetect [K.Normal] {H : Subgroup ↥K} {f g : ↥L → ℂ}
    (hf : f ∈ indFamDetect K H) (hg : g ∈ indFamDetect K H) (hne : f ≠ g) :
    cfInner f g = 0 :=
  NormalInducedFamily.cfInner_eq_zero_of_mem_indFam K (indFamDetect_subset_indFam_Irr K H hf)
    (indFamDetect_subset_indFam_Irr K H hg) hne

omit [Fintype G] in
theorem charInner_eq_zero_of_mem_indFamDetect [K.Normal] {H : Subgroup ↥K} {f g : ↥L → ℂ}
    (hf : f ∈ indFamDetect K H) (hg : g ∈ indFamDetect K H) (hne : f ≠ g) :
    charInner f g = 0 := by
  rw [charInner_eq_cfInner]
  exact cfInner_eq_zero_of_mem_indFamDetect hf hg hne

omit [Fintype G] in
theorem star_ne_self_of_mem_indFamDetect_of_odd_natCard [K.Normal] (hodd : Odd (Nat.card G))
    {H : Subgroup ↥K} {f : ↥L → ℂ} (hf : f ∈ indFamDetect K H) : star f ≠ f :=
  star_ne_self_of_mem_indFamDetect (odd_natCard_subgroup hodd L) hf

omit [Fintype G] in
theorem apply_eq_zero_of_mem_indFamDetect_of_notMem [K.Normal] {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L}
    (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    {f : ↥L → ℂ} (hf : f ∈ indFamDetect K (H.subgroupOf K)) {g : ↥L} (hg : g ∉ A ∪ {1}) :
    f g = 0 := by
  classical
  obtain ⟨θ, hθIrr, ⟨y, hyH, hy⟩, rfl⟩ := (mem_indFamDetect_subgroupOf K).1 hf
  have hθIrr' : θ ∈ Irr ↥K := by rw [Irr_eq_irrChar]; exact hθIrr
  have hnormal : (H.subgroupOf K).Normal := ‹H.Normal›.subgroupOf K
  have hzero : ∀ z : ↥K, (z : ↥L) ∉ A ∪ {1} → θ z = 0 := by
    intro z hz
    refine eq_zero_of_forall_mem_centralizer (H := H.subgroupOf K) hθIrr'
      ⟨y, Subgroup.mem_subgroupOf.2 hyH, hy⟩ ?_
    intro w hw hcomm
    by_contra hw1
    have hwH : (w : ↥L) ∈ H := Subgroup.mem_subgroupOf.1 hw
    have hw1' : (w : ↥L) ≠ 1 := fun hc => hw1 (Subtype.ext hc)
    have hc : (w : ↥L) * (z : ↥L) = (z : ↥L) * (w : ↥L) := by
      simpa using congrArg (Subtype.val : ↥K → ↥L) hcomm
    refine hz (Or.inl (hA _ hwH hw1' ⟨Subgroup.mem_inf.2 ⟨z.2,
      Subgroup.mem_centralizer_singleton_iff.2 hc.symm⟩, ?_⟩))
    exact fun hc1 => hz (Or.inr hc1)
  rw [indClassFun_apply]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)
  by_cases hm : t⁻¹ * g * t ∈ K
  · rw [dif_pos hm]
    refine hzero _ (fun hcon => hg ?_)
    rcases hcon with hcon | hcon
    · have h2 := mem_of_conj_image_eq_self hAconj t⁻¹ hcon
      rw [show t⁻¹⁻¹ * (t⁻¹ * g * t) * t⁻¹ = g by group] at h2
      exact Or.inl h2
    · have h1 : t⁻¹ * g * t = 1 := hcon
      refine Or.inr ?_
      calc g = t * (t⁻¹ * g * t) * t⁻¹ := by group
        _ = 1 := by rw [h1]; group
  · rw [dif_neg hm]

omit [Fintype G] in
theorem apply_eq_zero_of_mem_intSpanZeroAtOne [K.Normal] {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L}
    (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    {f : ↥L → ℂ} (hf : f ∈ intSpanZeroAtOne (indFamDetect K (H.subgroupOf K)))
    {g : ↥L} (hg : g ∉ A) : f g = 0 := by
  obtain ⟨hspan, h1⟩ := mem_intSpanZeroAtOne.1 hf
  rcases eq_or_ne g 1 with rfl | hg1
  · exact h1
  refine eq_zero_of_mem_span_of_forall_eq_zero (x := g) (fun c hc => ?_) hspan
  refine apply_eq_zero_of_mem_indFamDetect_of_notMem hAconj hA hc ?_
  simp only [Set.mem_union, Set.mem_singleton_iff]
  exact fun hc' => hc'.elim (fun h => hg h) fun h => hg1 h

omit [Fintype G] in
theorem mem_dadeDomain_of_mem_intSpanZeroAtOne [K.Normal] {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} {A₀ : Set G}
    (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀)
    {f : ↥L → ℂ} (hf : f ∈ intSpanZeroAtOne (indFamDetect K (H.subgroupOf K))) :
    f ∈ dadeDomain L A₀ := by
  refine mem_dadeDomain_of_mem_span_Irr ?_ ?_
  · exact Submodule.span_le.2 (fun g hg => mem_span_Irr_of_mem_indFamDetect hg)
      (mem_intSpanZeroAtOne.1 hf).1
  · intro x hx
    exact apply_eq_zero_of_mem_intSpanZeroAtOne hAconj hA hf
      (fun hmem => hx (hA₀ ⟨x, hmem, rfl⟩))

end Family

section Transfer

theorem dadeMapFun_add_of_mem {G : Type*} [Group G] {L : Subgroup G} (A₀ : Set G)
    (T : G → Subgroup G) (f g : ↥L → ℂ) :
    dadeMapFun L A₀ T (f + g) = dadeMapFun L A₀ T f + dadeMapFun L A₀ T g :=
  dadeMapFun_add L A₀ T f g

theorem dadeMapFun_apply_one_eq_zero {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {A₀ : Set G} {T : G → Subgroup G} (hD : IsDadeData L A₀ T) {f : ↥L → ℂ}
    (hf : f ∈ dadeDomain L A₀) : dadeMapFun L A₀ T f 1 = 0 := by
  have := dadeMap_one_eq_zero hD ⟨f, hf⟩
  rwa [coe_dadeMap hD ⟨f, hf⟩] at this

theorem cfInner_dadeMapFun {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {A₀ : Set G} {T : G → Subgroup G} (hD : IsDadeData L A₀ T) {f g : ↥L → ℂ}
    (hf : f ∈ dadeDomain L A₀) (hg : g ∈ dadeDomain L A₀) :
    cfInner (dadeMapFun L A₀ T f) (dadeMapFun L A₀ T g) = cfInner f g := by
  have := cfInner_dadeMap hD ⟨f, hf⟩ ⟨g, hg⟩
  rwa [coe_dadeMap hD ⟨f, hf⟩, coe_dadeMap hD ⟨g, hg⟩] at this

theorem dadeMapFun_mem_span_Irr {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {A₀ : Set G} {T : G → Subgroup G} (hD : IsDadeData L A₀ T) {f : ↥L → ℂ}
    (hf : f ∈ dadeDomain L A₀) (hfI : f ∈ Submodule.span ℤ (Irr ↥L)) :
    dadeMapFun L A₀ T f ∈ Submodule.span ℤ (Irr G) := by
  have := hD.dadeMap_mem_span_Irr hf hfI
  rwa [coe_dadeMap hD ⟨f, hf⟩] at this

end Transfer

end PrimeDadeSubcoherence

section DadeAux

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]

omit [Fintype G] [Fintype ↥L] in
theorem dadeMapFun_sum {A₀ : Set G} {T : G → Subgroup G} {ι : Type*} (s : Finset ι)
    (f : ι → ↥L → ℂ) :
    dadeMapFun L A₀ T (∑ i ∈ s, f i) = ∑ i ∈ s, dadeMapFun L A₀ T (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using dadeMapFun_smul L A₀ T 0 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dadeMapFun_add, ih]

theorem isAntirealIsometry_dadeMapFun_of_charSpanZero_subset {A₀ : Set G} {T : G → Subgroup G}
    (hD : IsDadeData L A₀ T) {X : Set (↥L → ℂ)} (hXIrr : X ⊆ Irr ↥L)
    (hXstar : ∀ χ ∈ X, star χ ∈ X) (hXne : ∀ χ ∈ X, star χ ≠ χ)
    (hdom : ∀ f ∈ charSpanZero X, f ∈ dadeDomain L A₀) :
    IsAntirealIsometry X (dadeMapFun L A₀ T) where
  subset_Irr := hXIrr
  star_mem := hXstar
  star_ne := hXne
  map_add f _ g _ := dadeMapFun_add L A₀ T f g
  map_mem f hf := PrimeDadeSubcoherence.dadeMapFun_mem_span_Irr hD (hdom f hf)
    (Submodule.span_mono hXIrr (charSpanZero_le X hf))
  inner_eq f hf g hg := PrimeDadeSubcoherence.cfInner_dadeMapFun hD (hdom f hf) (hdom g hg)
  apply_one f hf := PrimeDadeSubcoherence.dadeMapFun_apply_one_eq_zero hD (hdom f hf)
  map_star f _ := dadeMapFun_star L A₀ T f

theorem exists_dadeMapFun_sub_star_eq {A₀ : Set G} {T : G → Subgroup G}
    (hD : IsDadeData L A₀ T) {ξ : ↥L → ℂ} (hξ : ξ ∈ Irr ↥L) (hnr : ξ ≠ star ξ)
    (hdom : ∀ f ∈ charSpanZero ({ξ, star ξ} : Set (↥L → ℂ)), f ∈ dadeDomain L A₀) :
    ∃ ρ ∈ Irr G, star ρ ≠ ρ ∧ dadeMapFun L A₀ T (ξ - star ξ) = ρ - star ρ := by
  have hiso : IsAntirealIsometry ({ξ, star ξ} : Set (↥L → ℂ)) (dadeMapFun L A₀ T) := by
    refine isAntirealIsometry_dadeMapFun_of_charSpanZero_subset hD ?_ ?_ ?_ hdom
    · rintro g (rfl | rfl)
      · exact hξ
      · exact star_mem_Irr hξ
    · rintro g (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl (star_star _)
    · rintro g (rfl | rfl)
      · exact fun hc => hnr hc.symm
      · rw [star_star]; exact fun hc => hnr hc
  exact hiso.exists_root (Set.mem_insert _ _)

end DadeAux

namespace PrimeDadeSubcoherence

section Node

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [Fintype ↑(Irr ↥W₁)]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {A₀ : Set G} {T : G → Subgroup G}

theorem mem_Irr_or_exists_primeTIrow_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup ↥L} {f : ↥L → ℂ}
    (hf : f ∈ indFamDetect K (H.subgroupOf K)) :
    f ∈ Irr ↥L ∨ ∃ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ ∧ h.primeTIrow σ j = f := by
  have hKn : K.Normal := h.normal
  obtain ⟨θ, hθd, rfl⟩ := (mem_indFamDetect K).1 hf
  obtain ⟨hθirr, hθker⟩ := mem_irrDetect.1 hθd
  have hθ : θ ∈ Irr ↥K := by rw [Irr_eq_irrChar]; exact hθirr
  rcases h.xor_exists_primeTIres_eq hσ hθ with ⟨⟨j, hj, -⟩, -⟩ | ⟨⟨hirr, -⟩, -⟩
  · refine Or.inr ⟨j, ?_, ?_⟩
    · exact h.ne_principalIrr_of_not_subset_charValueKernel hσ (H := H) (by rw [hj]; exact hθker)
    · rw [← hj, h.indClassFun_primeTIres hσ]
  · exact Or.inl hirr

theorem primeTIrow_mem_indFamDetect (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup ↥L} (hWH : W₂ ≤ H)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIrow σ j ∈ indFamDetect K (H.subgroupOf K) := by
  refine (mem_indFamDetect K).2 ⟨h.primeTIres σ j, ?_, h.indClassFun_primeTIres hσ j⟩
  refine mem_irrDetect.2 ⟨?_, h.not_subset_charValueKernel_primeTIres hσ hWH hj⟩
  rw [← Irr_eq_irrChar]; exact h.primeTIres_mem_Irr hσ j

theorem primeTIrow_notMem_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    h.primeTIrow σ j ∉ Irr ↥L := by
  have hmem := h.indClassFun_notMem_Irr_primeTIres hσ j
  rwa [h.indClassFun_primeTIres hσ j] at hmem

theorem primeTIrow_injective (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j k : Irr ↥W₂}
    (hjk : h.primeTIrow σ j = h.primeTIrow σ k) : j = k := by
  classical
  by_contra hne
  have h0 := cfInner_primeTIrow_primeTIrow h hσ j k
  rw [if_neg hne, hjk, cfInner_primeTIrow_primeTIrow h hσ k k, if_pos rfl] at h0
  exact (Nat.cast_ne_zero.2 (Nat.card_pos (α := ↥W₁)).ne' : (Nat.card ↥W₁ : ℂ) ≠ 0) h0

noncomputable def rowSign (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L) (j : Irr ↥W₂) (b : Bool) : ℂ :=
  if b then h.primeTISign σ j else -h.primeTISign σ j

def rowCol (j : Irr ↥W₂) (b : Bool) : Irr ↥W₂ := if b then j else starIrr j

theorem rowCol_true (j : Irr ↥W₂) : rowCol j true = j := if_pos rfl

theorem rowCol_false (j : Irr ↥W₂) : rowCol j false = starIrr j := if_neg (by simp)

theorem rowSign_true (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    rowSign h σ j true = h.primeTISign σ j := if_pos rfl

theorem rowSign_false (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    rowSign h σ j false = -h.primeTISign σ j := if_neg (by simp)

theorem conj_rowSign (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) (b : Bool) :
    conj (rowSign h σ j b) = rowSign h σ j b := by
  cases b <;> simp [rowSign, h.conj_primeTISign]

theorem rowSign_mul_self (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) (b : Bool) :
    rowSign h σ j b * rowSign h σ j b = 1 := by
  cases b
  · simpa [rowSign] using h.primeTISign_mul_self (σ := σ) j
  · simpa [rowSign] using h.primeTISign_mul_self (σ := σ) j

theorem rowSign_eq_one_or_eq_neg_one (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) (b : Bool) :
    rowSign h σ j b = 1 ∨ rowSign h σ j b = -1 := by
  rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hs | hs <;> cases b <;>
    simp [rowSign, hs]

theorem rowCol_injective (h : IsPrimeCyclicTIHyp K W₁ W₂)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : Function.Injective (rowCol j) := by
  have hne : starIrr j ≠ j := starIrr_ne_self h.isCyclicTIPair.odd_natCard_right hj
  intro a b hab
  cases a <;> cases b
  · rfl
  · exfalso; rw [rowCol_false, rowCol_true] at hab; exact hne hab
  · exfalso; rw [rowCol_true, rowCol_false] at hab; exact hne hab.symm
  · rfl

noncomputable def rowElt (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (j : Irr ↥W₂) (p : Irr ↥W₁ × Bool) : G → ℂ :=
  rowSign h σ j p.2 •
    hW.prodCharEta ω (irrMapSubtype L W₁ p.1) (irrMapSubtype L W₂ (rowCol j p.2))

theorem rowElt_def (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (j : Irr ↥W₂) (p : Irr ↥W₁ × Bool) :
    rowElt h hW σ ω j p = rowSign h σ j p.2 •
      hW.prodCharEta ω (irrMapSubtype L W₁ p.1) (irrMapSubtype L W₂ (rowCol j p.2)) := (rfl)

open scoped Classical in
noncomputable def rowBlock (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (j : Irr ↥W₂) : Finset (G → ℂ) :=
  Finset.univ.image (rowElt h hW σ ω j)

theorem mem_rowBlock (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (j : Irr ↥W₂) {r : G → ℂ} :
    r ∈ rowBlock h hW σ ω j ↔ ∃ p : Irr ↥W₁ × Bool, rowElt h hW σ ω j p = r := by
  classical
  rw [rowBlock]; simp

theorem coe_rowBlock (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (j : Irr ↥W₂) :
    (rowBlock h hW σ ω j : Set (G → ℂ))
      = Set.range (fun i : Irr ↥W₁ => h.primeTISign σ j •
          hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j))
        ∪ Set.range (fun i : Irr ↥W₁ => -(h.primeTISign σ j •
          hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ (starIrr j)))) := by
  ext r
  rw [Finset.mem_coe, mem_rowBlock]
  constructor
  · rintro ⟨⟨i, b⟩, rfl⟩
    cases b
    · refine Or.inr ⟨i, ?_⟩
      rw [rowElt_def, rowSign_false, rowCol_false, neg_smul]
    · exact Or.inl ⟨i, by rw [rowElt_def, rowSign_true, rowCol_true]⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨(i, true), by rw [rowElt_def, rowSign_true, rowCol_true]⟩
    · exact ⟨(i, false), by rw [rowElt_def, rowSign_false, rowCol_false, neg_smul]⟩

theorem cfInner_rowElt (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) {p q : Irr ↥W₁ × Bool} (hpq : p ≠ q) :
    cfInner (rowElt h hW σ ω j p) (rowElt h hW σ ω j q) = 0 := by
  classical
  rw [rowElt_def, rowElt_def, cfInner_smul_left, cfInner_smul_right, conj_rowSign,
    hW.cfInner_prodCharEta hω, if_neg, mul_zero, mul_zero]
  rintro ⟨h1, h2⟩
  exact hpq (Prod.ext (irrMapSubtype_injective L W₁ h1)
    (rowCol_injective h hj (irrMapSubtype_injective L W₂ h2)))

theorem cfInner_rowElt_self (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (j : Irr ↥W₂) (p : Irr ↥W₁ × Bool) :
    cfInner (rowElt h hW σ ω j p) (rowElt h hW σ ω j p) = 1 := by
  classical
  rw [rowElt_def, cfInner_smul_left, cfInner_smul_right, conj_rowSign,
    hW.cfInner_prodCharEta hω, if_pos ⟨rfl, rfl⟩, mul_one, rowSign_mul_self]

theorem rowElt_injective (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    Function.Injective (rowElt h hW σ ω j) := by
  intro p q hpq
  by_contra hne
  have h0 : cfInner (rowElt h hW σ ω j p) (rowElt h hW σ ω j q) = 0 :=
    cfInner_rowElt h hW hω hj hne
  rw [hpq, cfInner_rowElt_self h hW hω j q] at h0
  exact one_ne_zero h0

theorem rowElt_mem_span_Irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (j : Irr ↥W₂) (p : Irr ↥W₁ × Bool) :
    rowElt h hW σ ω j p ∈ Submodule.span ℤ (Irr G) := by
  have hmem := mem_span_Irr_of_mem_virtualChars
    (hW.prodCharEta_mem_virtualChars hω (irrMapSubtype L W₁ p.1)
      (irrMapSubtype L W₂ (rowCol j p.2)))
  rw [rowElt_def]
  rcases rowSign_eq_one_or_eq_neg_one (σ := σ) h j p.2 with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rw [neg_one_smul]; exact Submodule.neg_mem _ hmem

theorem sum_rowBlock (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ∑ r ∈ rowBlock h hW σ ω j, r
      = h.primeTISign σ j • ∑ i : Irr ↥W₁,
          (hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
            - hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ (starIrr j))) := by
  classical
  rw [rowBlock, Finset.sum_image (fun p _ q _ hpq => rowElt_injective h hW hω hj hpq),
    Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool, rowElt_def, rowElt_def, rowSign_true, rowSign_false, rowCol_true,
    rowCol_false, smul_sub, neg_smul]
  ring

theorem dadeMapFun_primeTIrow_sub_starIrr
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H) {A : Set ↥L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    dadeMapFun L A₀ T (h.primeTIrow σ j - h.primeTIrow σ (starIrr j))
      = h.primeTISign σ j • ∑ i : Irr ↥W₁,
          ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
            - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ (starIrr j))) := by
  classical
  have hjs : starIrr j ≠ principalIrr ↥W₂ := starIrr_ne_principalIrr hj
  have hone : ∀ i : Irr ↥W₁, h.primeTIirr σ i j 1 = h.primeTIirr σ i (starIrr j) 1 :=
    fun i => h.primeTIirr_one_starIrr_eq hσ i j
  have hsplit : h.primeTIrow σ j - h.primeTIrow σ (starIrr j)
      = ∑ i : Irr ↥W₁, (h.primeTIirr σ i j - h.primeTIirr σ i (starIrr j)) := by
    rw [IsPrimeCyclicTIHyp.primeTIrow_def, IsPrimeCyclicTIHyp.primeTIrow_def,
      ← Finset.sum_sub_distrib]
  rw [hsplit, dadeMapFun_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmem := h.primeTIirr_sub_mem_dadeDomain hσ hWH hA hA₀ i hj hjs (hone i)
  rw [← coe_dadeMap hD ⟨_, hmem⟩]
  exact h.dadeMap_primeTIirr_sub_eq hσ hWH hA hA₀ hD hstab hdisj hω i hj hjs (hone i)

open scoped Classical in
noncomputable def irrBlock (τ : (↥L → ℂ) → G → ℂ) (χ : ↥L → ℂ) : Finset (G → ℂ) :=
  {antirealRoot (τ (χ - star χ)), -star (antirealRoot (τ (χ - star χ)))}

theorem mem_irrBlock {τ : (↥L → ℂ) → G → ℂ} {χ : ↥L → ℂ} {r : G → ℂ} :
    r ∈ irrBlock τ χ ↔ r = antirealRoot (τ (χ - star χ))
      ∨ r = -star (antirealRoot (τ (χ - star χ))) := by
  classical
  rw [irrBlock]; simp

theorem ne_neg_star_of_mem_Irr {η : G → ℂ} (h1 : η ∈ Irr G) (h2 : star η ≠ η) :
    η ≠ -star η := by
  intro hc
  have h4 : cfInner η (star η) = 0 :=
    cfInner_eq_zero_of_mem_Irr h1 (star_mem_Irr h1) (Ne.symm h2)
  have h5 : cfInner η (star η) = -1 := by
    nth_rewrite 1 [hc]
    rw [cfInner_neg_left, cfInner_self_of_mem_Irr (star_mem_Irr h1)]
  rw [h5] at h4
  norm_num at h4

theorem antirealRoot_ne_neg_star {z : G → ℂ}
    (hz : ∃ η ∈ Irr G, star η ≠ η ∧ z = η - star η) :
    antirealRoot z ≠ -star (antirealRoot z) :=
  ne_neg_star_of_mem_Irr (antirealRoot_mem_Irr hz) (star_antirealRoot_ne hz)

theorem sum_irrBlock {τ : (↥L → ℂ) → G → ℂ} {χ : ↥L → ℂ}
    (hz : ∃ η ∈ Irr G, star η ≠ η ∧ τ (χ - star χ) = η - star η) :
    ∑ r ∈ irrBlock τ χ, r = τ (χ - star χ) := by
  classical
  have key := sub_star_antirealRoot hz
  rw [irrBlock, Finset.sum_pair (antirealRoot_ne_neg_star hz)]
  linear_combination (norm := module) key

theorem cfInner_irrBlock_self {τ : (↥L → ℂ) → G → ℂ} {χ : ↥L → ℂ}
    (hz : ∃ η ∈ Irr G, star η ≠ η ∧ τ (χ - star χ) = η - star η)
    {r : G → ℂ} (hr : r ∈ irrBlock τ χ) : cfInner r r = 1 := by
  have h1 : antirealRoot (τ (χ - star χ)) ∈ Irr G := antirealRoot_mem_Irr hz
  rcases mem_irrBlock.1 hr with rfl | rfl
  · exact cfInner_self_of_mem_Irr h1
  · rw [cfInner_neg_left, cfInner_neg_right, neg_neg]
    exact cfInner_self_of_mem_Irr (star_mem_Irr h1)

theorem cfInner_irrBlock_of_ne {τ : (↥L → ℂ) → G → ℂ} {χ : ↥L → ℂ}
    (hz : ∃ η ∈ Irr G, star η ≠ η ∧ τ (χ - star χ) = η - star η)
    {r s : G → ℂ} (hr : r ∈ irrBlock τ χ) (hs : s ∈ irrBlock τ χ) (hrs : r ≠ s) :
    cfInner r s = 0 := by
  have h1 : antirealRoot (τ (χ - star χ)) ∈ Irr G := antirealRoot_mem_Irr hz
  have h2 : star (antirealRoot (τ (χ - star χ))) ≠ antirealRoot (τ (χ - star χ)) :=
    star_antirealRoot_ne hz
  rcases mem_irrBlock.1 hr with rfl | rfl <;> rcases mem_irrBlock.1 hs with rfl | rfl
  · exact absurd rfl hrs
  · rw [cfInner_neg_right, cfInner_eq_zero_of_mem_Irr h1 (star_mem_Irr h1) (Ne.symm h2), neg_zero]
  · rw [cfInner_neg_left, cfInner_eq_zero_of_mem_Irr (star_mem_Irr h1) h1 h2, neg_zero]
  · exact absurd rfl hrs

theorem irrBlock_mem_span_Irr {τ : (↥L → ℂ) → G → ℂ} {χ : ↥L → ℂ}
    (hz : ∃ η ∈ Irr G, star η ≠ η ∧ τ (χ - star χ) = η - star η)
    {r : G → ℂ} (hr : r ∈ irrBlock τ χ) : r ∈ Submodule.span ℤ (Irr G) := by
  have h1 : antirealRoot (τ (χ - star χ)) ∈ Irr G := antirealRoot_mem_Irr hz
  rcases mem_irrBlock.1 hr with rfl | rfl
  · exact Submodule.subset_span h1
  · exact Submodule.neg_mem _ (Submodule.subset_span (star_mem_Irr h1))

theorem cfInner_of_disjoint_pair {η ρ : G → ℂ} (hη : η ∈ Irr G) (hρ : ρ ∈ Irr G)
    (hd : Disjoint ({η, star η} : Set (G → ℂ)) ({ρ, star ρ} : Set (G → ℂ)))
    {a b : G → ℂ} (ha : a = η ∨ a = -star η) (hb : b = ρ ∨ b = -star ρ) :
    cfInner a b = 0 := by
  have hdd := Set.disjoint_left.1 hd
  have h1 : η ≠ ρ := fun hc => hdd (Set.mem_insert _ _) (hc ▸ Set.mem_insert _ _)
  have h2 : η ≠ star ρ := fun hc =>
    hdd (Set.mem_insert _ _) (hc ▸ Set.mem_insert_of_mem _ rfl)
  have h3 : star η ≠ ρ := fun hc =>
    hdd (Set.mem_insert_of_mem _ rfl) (hc ▸ Set.mem_insert _ _)
  have h4 : star η ≠ star ρ := fun hc =>
    hdd (Set.mem_insert_of_mem _ rfl) (hc ▸ Set.mem_insert_of_mem _ rfl)
  have hsη := star_mem_Irr hη
  have hsρ := star_mem_Irr hρ
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact cfInner_eq_zero_of_mem_Irr hη hρ h1
  · rw [cfInner_neg_right, cfInner_eq_zero_of_mem_Irr hη hsρ h2, neg_zero]
  · rw [cfInner_neg_left, cfInner_eq_zero_of_mem_Irr hsη hρ h3, neg_zero]
  · rw [cfInner_neg_left, cfInner_neg_right, cfInner_eq_zero_of_mem_Irr hsη hsρ h4,
      neg_zero, neg_zero]

theorem rowCol_ne_rowCol {j k : Irr ↥W₂} (h1 : k ≠ j) (h2 : k ≠ starIrr j) (b c : Bool) :
    rowCol j b ≠ rowCol k c := by
  have hinj : Function.Injective (starIrr (X := ↥W₂)) := starIrr_involutive.injective
  cases b <;> cases c <;> simp only [rowCol_true, rowCol_false]
  · exact fun hc => h1 (hinj hc).symm
  · exact fun hc => h2 hc.symm
  · exact fun hc => h2 (starIrr_starIrr k ▸ (congrArg starIrr hc)).symm
  · exact fun hc => h1 hc.symm

theorem cfInner_rowBlock_rowBlock (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {j k : Irr ↥W₂} (h1 : k ≠ j) (h2 : k ≠ starIrr j)
    {r s : G → ℂ} (hr : r ∈ rowBlock h hW σ ω j) (hs : s ∈ rowBlock h hW σ ω k) :
    cfInner r s = 0 := by
  classical
  obtain ⟨p, rfl⟩ := (mem_rowBlock h hW j).1 hr
  obtain ⟨q, rfl⟩ := (mem_rowBlock h hW k).1 hs
  rw [rowElt_def, rowElt_def, cfInner_smul_left, cfInner_smul_right,
    hW.cfInner_prodCharEta hω, if_neg, mul_zero, mul_zero]
  rintro ⟨-, h3⟩
  exact rowCol_ne_rowCol h1 h2 p.2 q.2 (irrMapSubtype_injective L W₂ h3)

theorem cfInner_rowBlock_of_isOrthogonal_prodCharEta (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    {r : G → ℂ}
    (hr : ∀ (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)),
      cfInner r (hW.prodCharEta ω a b) = 0)
    {j : Irr ↥W₂} {s : G → ℂ} (hs : s ∈ rowBlock h hW σ ω j) : cfInner r s = 0 := by
  obtain ⟨p, rfl⟩ := (mem_rowBlock h hW j).1 hs
  rw [rowElt_def, cfInner_smul_right, hr, mul_zero]

theorem cfInner_of_isOrthogonal_prodCharEta_rowBlock (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    {r : G → ℂ}
    (hr : ∀ (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)),
      cfInner r (hW.prodCharEta ω a b) = 0)
    {j : Irr ↥W₂} {s : G → ℂ} (hs : s ∈ rowBlock h hW σ ω j) : cfInner s r = 0 := by
  rw [← conj_cfInner, cfInner_rowBlock_of_isOrthogonal_prodCharEta h hW hr hs, map_zero]

theorem coe_rowBlock_starIrr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (j : Irr ↥W₂) :
    (rowBlock h hW σ ω (starIrr j) : Set (G → ℂ))
      = (fun r => -r) '' (rowBlock h hW σ ω j : Set (G → ℂ)) := by
  classical
  rw [coe_rowBlock, coe_rowBlock, h.primeTISign_starIrr_eq hσ j, starIrr_starIrr,
    Set.image_union, ← Set.range_comp, ← Set.range_comp]
  refine (Set.union_comm _ _).trans ?_
  congr 1 <;> · ext r; simp [Function.comp]

theorem coe_irrBlock_star {τ : (↥L → ℂ) → G → ℂ} {χ : ↥L → ℂ}
    (hroot : antirealRoot (τ (star χ - star (star χ)))
      = star (antirealRoot (τ (χ - star χ)))) :
    (irrBlock τ (star χ) : Set (G → ℂ)) = (fun r => -r) '' (irrBlock τ χ : Set (G → ℂ)) := by
  classical
  ext r
  rw [Finset.mem_coe, mem_irrBlock]
  simp only [Set.mem_image, Finset.mem_coe, mem_irrBlock]
  rw [hroot, star_star]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨-star (antirealRoot (τ (χ - star χ))), Or.inr rfl, neg_neg _⟩
    · exact ⟨antirealRoot (τ (χ - star χ)), Or.inl rfl, rfl⟩
  · rintro ⟨s, (rfl | rfl), rfl⟩
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)

noncomputable def irrPart (K : Subgroup ↥L) (H : Subgroup ↥K) : Set (↥L → ℂ) :=
  indFamDetect K H ∩ Irr ↥L

theorem mem_irrPart {H : Subgroup ↥K} {f : ↥L → ℂ} :
    f ∈ irrPart K H ↔ f ∈ indFamDetect K H ∧ f ∈ Irr ↥L := Iff.rfl

theorem isAntirealIsometry_irrPart [K.Normal] (hodd : Odd (Nat.card G))
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀) (hD : IsDadeData L A₀ T) :
    IsAntirealIsometry (irrPart K (H.subgroupOf K)) (dadeMapFun L A₀ T) := by
  refine isAntirealIsometry_dadeMapFun_of_charSpanZero_subset hD (fun f hf => hf.2)
    (fun f hf => ⟨star_mem_indFamDetect hf.1, star_mem_Irr hf.2⟩)
    (fun f hf => star_ne_self_of_mem_indFamDetect_of_odd_natCard hodd hf.1) ?_
  intro f hf
  obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeDomain_of_mem_intSpanZeroAtOne hAconj hA hA₀ ?_
  exact mem_intSpanZeroAtOne.2
    ⟨Submodule.span_le.2 (fun g hg => Submodule.subset_span hg.1) hspan, h1⟩

theorem dadeMapFun_sub_star_apply_eq_zero_of_mem_cyclicTIDiff [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K))
    {v : G} (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype)) :
    dadeMapFun L A₀ T (χ - star χ) v = 0 := by
  have hmem : χ - star χ ∈ intSpanZeroAtOne (indFamDetect K (H.subgroupOf K)) := by
    refine mem_intSpanZeroAtOne.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hχ)
      (Submodule.subset_span (star_mem_indFamDetect hχ)), ?_⟩
    simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def]
    rw [(isCharacter_of_mem_indFamDetect hχ).conj_apply_one, sub_self]
  have hdom : χ - star χ ∈ dadeDomain L A₀ :=
    mem_dadeDomain_of_mem_intSpanZeroAtOne hAconj hA
      ((Set.image_mono subset_bridgeSupport_left).trans hA₀) hmem
  rw [← image_cyclicTIset_eq] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have hxA : (x : G) ∈ A₀ := hA₀ ⟨x,
    cyclicTIsetConj_subset_bridgeSupport (cyclicTIset_subset_cyclicTIsetConj _ _ hx), rfl⟩
  have hxK : (x : ↥L) ∉ K := h.notMem_of_mem_cyclicTIset hx
  have h0 : χ x = 0 := eq_zero_of_mem_indFamDetect_of_notMem K hχ hxK
  rw [← coe_dadeMap hD ⟨_, hdom⟩, dadeMap_apply_mem hD ⟨_, hdom⟩ hxA]
  have hx' : (⟨(x : G), hD.mem_of_mem hxA⟩ : ↥L) = x := Subtype.ext rfl
  simp only [hx', Pi.sub_apply, Pi.star_apply, h0]
  simp

theorem cfInner_prodCharEta_eq_zero_of_sub_star_eq_zero
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {ρ : G → ℂ} (hρ : ρ ∈ Irr G) (hρnr : star ρ ≠ ρ)
    (hvan : ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype),
      (ρ - star ρ) v = 0)
    (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)) :
    cfInner ρ (hW.prodCharEta ω a b) = 0 ∧ cfInner (star ρ) (hW.prodCharEta ω a b) = 0 := by
  have hχ : ((hW.basisProdIrr (a, b) : classFun ↥((W₁ ⊔ W₂).map L.subtype)) :
      ↥((W₁ ⊔ W₂).map L.subtype) → ℂ) ∈ Irr ↥((W₁ ⊔ W₂).map L.subtype) := by
    rw [hW.coe_basisProdIrr_apply]
    exact hW.prodChar_mem_Irr a.2 b.2
  have h1 : IsOrthogonal ρ (hW.prodCharEta ω a b) := by
    have hsi : ρ ∈ signedIrr G := Irr_subset_signedIrr hρ
    have hne : ρ ≠ fun x => conj (ρ x) := by
      rw [← star_eq_conj_fun]
      exact fun hc => hρnr hc.symm
    have hz : ∀ x ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
        (W₂.map L.subtype), (ρ - fun z => conj (ρ z)) x = 0 := by
      intro x hx
      simpa [star_eq_conj_fun] using hvan x hx
    have hres := hW.isOrthogonal_apply_of_ne_conj hω hsi hne hz hχ
    rwa [← hW.prodCharEta_eq_coe_apply] at hres
  have h2 : IsOrthogonal (star ρ) (hW.prodCharEta ω a b) := by
    have hsi : star ρ ∈ signedIrr G := Irr_subset_signedIrr (star_mem_Irr hρ)
    have hne : star ρ ≠ fun x => conj (star ρ x) := by
      rw [← star_eq_conj_fun, star_star]
      exact hρnr
    have hz : ∀ x ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
        (W₂.map L.subtype), (star ρ - fun z => conj (star ρ z)) x = 0 := by
      intro x hx
      have hx0 := hvan x hx
      simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def, starRingEnd_self_apply] at hx0 ⊢
      linear_combination -hx0
    have hres := hW.isOrthogonal_apply_of_ne_conj hω hsi hne hz hχ
    rwa [← hW.prodCharEta_eq_coe_apply] at hres
  exact ⟨isOrthogonal_iff.1 h1, isOrthogonal_iff.1 h2⟩

theorem exists_root_of_mem_indFamDetect_of_mem_Irr [K.Normal] (hodd : Odd (Nat.card G))
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀) (hD : IsDadeData L A₀ T)
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K)) (hχIrr : χ ∈ Irr ↥L) :
    ∃ η ∈ Irr G, star η ≠ η ∧ dadeMapFun L A₀ T (χ - star χ) = η - star η :=
  (isAntirealIsometry_irrPart hodd hAconj hA hA₀ hD).exists_root (mem_irrPart.2 ⟨hχ, hχIrr⟩)

theorem isOrthogonal_irrBlock_prodCharEta [K.Normal] (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀) (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K)) (hχIrr : χ ∈ Irr ↥L)
    {r : G → ℂ} (hr : r ∈ irrBlock (dadeMapFun L A₀ T) χ)
    (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)) :
    cfInner r (hW.prodCharEta ω a b) = 0 := by
  have hAA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀ :=
    (Set.image_mono subset_bridgeSupport_left).trans hA₀
  have hex := exists_root_of_mem_indFamDetect_of_mem_Irr hodd hAconj hA hAA₀ hD hχ hχIrr
  set ρ := antirealRoot (dadeMapFun L A₀ T (χ - star χ)) with hρdef
  have hρ : ρ ∈ Irr G := antirealRoot_mem_Irr hex
  have hρnr : star ρ ≠ ρ := star_antirealRoot_ne hex
  have hvan : ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype), (ρ - star ρ) v = 0 := by
    intro v hv
    rw [sub_star_antirealRoot hex]
    exact dadeMapFun_sub_star_apply_eq_zero_of_mem_cyclicTIDiff h hAconj hA hA₀ hD hχ hv
  obtain ⟨h1, h2⟩ := cfInner_prodCharEta_eq_zero_of_sub_star_eq_zero hW hω hρ hρnr hvan a b
  rcases mem_irrBlock.1 hr with rfl | rfl
  · exact h1
  · rw [cfInner_neg_left, h2, neg_zero]

theorem cfInner_irrBlock_irrBlock [K.Normal] (hodd : Odd (Nat.card G))
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀) (hD : IsDadeData L A₀ T)
    {χ ψ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K)) (hχIrr : χ ∈ Irr ↥L)
    (hψ : ψ ∈ indFamDetect K (H.subgroupOf K)) (hψIrr : ψ ∈ Irr ↥L)
    (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ)
    {r s : G → ℂ} (hr : r ∈ irrBlock (dadeMapFun L A₀ T) χ)
    (hs : s ∈ irrBlock (dadeMapFun L A₀ T) ψ) : cfInner r s = 0 := by
  set hiso := isAntirealIsometry_irrPart (K := K) (A₀ := A₀) (T := T) hodd hAconj hA hA₀ hD
    with hisodef
  have hχ' : χ ∈ irrPart K (H.subgroupOf K) := mem_irrPart.2 ⟨hχ, hχIrr⟩
  have hψ' : ψ ∈ irrPart K (H.subgroupOf K) := mem_irrPart.2 ⟨hψ, hψIrr⟩
  refine cfInner_of_disjoint_pair (hiso.root_mem_Irr hχ') (hiso.root_mem_Irr hψ')
    (hiso.disjoint_root_pair hχ' hψ' h1 h2) ?_ ?_
  · rcases mem_irrBlock.1 hr with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
  · rcases mem_irrBlock.1 hs with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh

open scoped Classical in
noncomputable def blockMap (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (A₀ : Set G) (T : G → Subgroup G) (f : ↥L → ℂ) : Finset (G → ℂ) :=
  if hex : ∃ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ ∧ h.primeTIrow σ j = f then
    rowBlock h hW σ ω hex.choose
  else irrBlock (dadeMapFun L A₀ T) f

theorem blockMap_row (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    blockMap h hW σ ω A₀ T (h.primeTIrow σ j) = rowBlock h hW σ ω j := by
  classical
  have hex : ∃ k : Irr ↥W₂, k ≠ principalIrr ↥W₂ ∧ h.primeTIrow σ k = h.primeTIrow σ j :=
    ⟨j, hj, rfl⟩
  rw [blockMap, dif_pos hex]
  congr 1
  exact primeTIrow_injective h hσ hex.choose_spec.2

theorem blockMap_irr (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    {f : ↥L → ℂ} (hf : f ∈ Irr ↥L) :
    blockMap h hW σ ω A₀ T f = irrBlock (dadeMapFun L A₀ T) f := by
  classical
  rw [blockMap, dif_neg]
  rintro ⟨j, hj, rfl⟩
  exact primeTIrow_notMem_Irr h hσ j hf

theorem blockMap_cases (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    {H : Subgroup ↥L} {f : ↥L → ℂ} (hf : f ∈ indFamDetect K (H.subgroupOf K)) :
    (f ∈ Irr ↥L ∧ blockMap h hW σ ω A₀ T f = irrBlock (dadeMapFun L A₀ T) f)
      ∨ ∃ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ ∧ h.primeTIrow σ j = f
          ∧ blockMap h hW σ ω A₀ T f = rowBlock h hW σ ω j := by
  rcases mem_Irr_or_exists_primeTIrow_eq h hσ hf with hirr | ⟨j, hj, rfl⟩
  · exact Or.inl ⟨hirr, blockMap_irr h hσ hW hirr⟩
  · exact Or.inr ⟨j, hj, rfl, blockMap_row h hσ hW hj⟩

theorem blockMap_subset_span_Irr [K.Normal] (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀) (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K))
    {r : G → ℂ} (hr : r ∈ blockMap h hW σ ω A₀ T χ) : r ∈ Submodule.span ℤ (Irr G) := by
  rcases blockMap_cases h hσ hW hχ with ⟨hirr, heq⟩ | ⟨j, hj, hrow, heq⟩
  · rw [heq] at hr
    exact irrBlock_mem_span_Irr
      (exists_root_of_mem_indFamDetect_of_mem_Irr hodd hAconj hA hA₀ hD hχ hirr) hr
  · rw [heq] at hr
    obtain ⟨p, rfl⟩ := (mem_rowBlock h hW j).1 hr
    exact rowElt_mem_span_Irr h hW hω j p

theorem cfInner_blockMap_self [K.Normal] (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀) (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K))
    {r : G → ℂ} (hr : r ∈ blockMap h hW σ ω A₀ T χ) : cfInner r r = 1 := by
  rcases blockMap_cases h hσ hW hχ with ⟨hirr, heq⟩ | ⟨j, hj, hrow, heq⟩
  · rw [heq] at hr
    exact cfInner_irrBlock_self
      (exists_root_of_mem_indFamDetect_of_mem_Irr hodd hAconj hA hA₀ hD hχ hirr) hr
  · rw [heq] at hr
    obtain ⟨p, rfl⟩ := (mem_rowBlock h hW j).1 hr
    exact cfInner_rowElt_self h hW hω j p

theorem cfInner_blockMap_of_ne [K.Normal] (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀) (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K))
    {r s : G → ℂ} (hr : r ∈ blockMap h hW σ ω A₀ T χ) (hs : s ∈ blockMap h hW σ ω A₀ T χ)
    (hrs : r ≠ s) : cfInner r s = 0 := by
  rcases blockMap_cases h hσ hW hχ with ⟨hirr, heq⟩ | ⟨j, hj, hrow, heq⟩
  · rw [heq] at hr hs
    exact cfInner_irrBlock_of_ne
      (exists_root_of_mem_indFamDetect_of_mem_Irr hodd hAconj hA hA₀ hD hχ hirr) hr hs hrs
  · rw [heq] at hr hs
    obtain ⟨p, rfl⟩ := (mem_rowBlock h hW j).1 hr
    obtain ⟨q, rfl⟩ := (mem_rowBlock h hW j).1 hs
    exact cfInner_rowElt h hW hω hj fun hc => hrs (by rw [hc])

theorem dadeMapFun_sub_star_eq_sum_blockMap [K.Normal] (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀) (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K)) :
    dadeMapFun L A₀ T (χ - star χ)
      = ∑ r ∈ blockMap h (h.isCyclicTIPair_map_subtype hstab hdisj) σ ω A₀ T χ, r := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  have hAA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀ :=
    (Set.image_mono subset_bridgeSupport_left).trans hA₀
  rcases blockMap_cases h hσ hW hχ (A₀ := A₀) (T := T) with ⟨hirr, heq⟩ | ⟨j, hj, hrow, heq⟩
  · rw [heq, sum_irrBlock
      (exists_root_of_mem_indFamDetect_of_mem_Irr hodd hAconj hA hAA₀ hD hχ hirr)]
  · subst hrow
    rw [heq, sum_rowBlock h hW hω hj,
      ← dadeMapFun_primeTIrow_sub_starIrr h hσ hWH hA hA₀ hD hstab hdisj hω hj,
      h.primeTIrow_starIrr_eq_star hσ j]

theorem cfInner_blockMap_blockMap [K.Normal] (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀) (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {χ ψ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K))
    (hψ : ψ ∈ indFamDetect K (H.subgroupOf K)) (h1 : ψ ≠ χ) (h2 : ψ ≠ star χ)
    {r s : G → ℂ} (hr : r ∈ blockMap h hW σ ω A₀ T χ) (hs : s ∈ blockMap h hW σ ω A₀ T ψ) :
    cfInner r s = 0 := by
  have hAA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀ :=
    (Set.image_mono subset_bridgeSupport_left).trans hA₀
  rcases blockMap_cases h hσ hW hχ (A₀ := A₀) (T := T) with ⟨hirrχ, heqχ⟩ | ⟨j, hj, hrowχ, heqχ⟩
  · rcases blockMap_cases h hσ hW hψ (A₀ := A₀) (T := T) with ⟨hirrψ, heqψ⟩ | ⟨k, hk, hrowψ, heqψ⟩
    · rw [heqχ] at hr; rw [heqψ] at hs
      exact cfInner_irrBlock_irrBlock hodd hAconj hA hAA₀ hD hχ hirrχ hψ hirrψ h1 h2 hr hs
    · rw [heqχ] at hr; rw [heqψ] at hs
      exact cfInner_rowBlock_of_isOrthogonal_prodCharEta (σ := σ) h hW
        (fun a b => isOrthogonal_irrBlock_prodCharEta hodd h hAconj hA hA₀ hD hW hω hχ hirrχ hr
          a b) hs
  · rcases blockMap_cases h hσ hW hψ (A₀ := A₀) (T := T) with ⟨hirrψ, heqψ⟩ | ⟨k, hk, hrowψ, heqψ⟩
    · rw [heqχ] at hr; rw [heqψ] at hs
      exact cfInner_of_isOrthogonal_prodCharEta_rowBlock (σ := σ) h hW
        (fun a b => isOrthogonal_irrBlock_prodCharEta hodd h hAconj hA hA₀ hD hW hω hψ hirrψ hs
          a b) hr
    · rw [heqχ] at hr; rw [heqψ] at hs
      refine cfInner_rowBlock_rowBlock h hW hω ?_ ?_ hr hs
      · intro hc; exact h1 (by rw [← hrowχ, ← hrowψ, hc])
      · intro hc
        refine h2 ?_
        rw [← hrowψ, hc, ← hrowχ]
        exact h.primeTIrow_starIrr_eq_star hσ j

theorem coe_blockMap_star [K.Normal] (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal]
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀) (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    {χ : ↥L → ℂ} (hχ : χ ∈ indFamDetect K (H.subgroupOf K)) :
    (blockMap h hW σ ω A₀ T (star χ) : Set (G → ℂ))
      = (fun r => -r) '' (blockMap h hW σ ω A₀ T χ : Set (G → ℂ)) := by
  classical
  rcases mem_Irr_or_exists_primeTIrow_eq h hσ hχ with hirr | ⟨j, hj, rfl⟩
  · have hsirr : star χ ∈ Irr ↥L := star_mem_Irr hirr
    rw [blockMap_irr h hσ hW hsirr, blockMap_irr h hσ hW hirr]
    exact coe_irrBlock_star
      ((isAntirealIsometry_irrPart hodd hAconj hA hA₀ hD).root_star (mem_irrPart.2 ⟨hχ, hirr⟩))
  · have hjs : starIrr j ≠ principalIrr ↥W₂ := starIrr_ne_principalIrr hj
    have hstar : star (h.primeTIrow σ j) = h.primeTIrow σ (starIrr j) :=
      (h.primeTIrow_starIrr_eq_star hσ j).symm
    rw [hstar, blockMap_row h hσ hW hjs, blockMap_row h hσ hW hj]
    exact coe_rowBlock_starIrr h hσ hW j

theorem exists_isSubcoherent_indFamDetect (hodd : Odd (Nat.card G))
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H) (hHK : H ≤ K)
    {A : Set ↥L} (hAconj : ∀ t : ↥L, (fun a => t⁻¹ * a * t) '' A = A)
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {S : Finset (↥L → ℂ)} (hS : (S : Set (↥L → ℂ)) = indFamDetect K (H.subgroupOf K)) :
    ∃ R : (↥L → ℂ) → Finset (G → ℂ),
      IsSubcoherent S (dadeMapFun L A₀ T) R ∧
      (∀ χ ∈ S, (R (star χ) : Set (G → ℂ)) = (fun r => -r) '' (R χ : Set (G → ℂ))) ∧
      (∀ χ ∈ S, χ ∈ Irr ↥L → ∀ r ∈ R χ, ∀ (i : Irr ↥(W₁.map L.subtype))
        (j : Irr ↥(W₂.map L.subtype)),
          IsOrthogonal r ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω i j)) ∧
      (∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ →
        h.primeTIrow σ j ∈ S ∧
        (R (h.primeTIrow σ j) : Set (G → ℂ))
          = Set.range (fun i : Irr ↥W₁ => h.primeTISign σ j •
              (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
                (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j))
            ∪ Set.range (fun i : Irr ↥W₁ => -(h.primeTISign σ j •
              (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
                (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ (starIrr j))))) := by
  classical
  have hKn : K.Normal := h.normal
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  have hmem : ∀ f : ↥L → ℂ, f ∈ S → f ∈ indFamDetect K (H.subgroupOf K) := by
    intro f hf; rw [← Finset.mem_coe, hS] at hf; exact hf
  have hAA₀ : (fun x : ↥L => (x : G)) '' A ⊆ A₀ :=
    (Set.image_mono subset_bridgeSupport_left).trans hA₀
  have hdom : ∀ f ∈ intSpanZeroAtOne (S : Set (↥L → ℂ)), f ∈ dadeDomain L A₀ := by
    intro f hf
    rw [hS] at hf
    exact mem_dadeDomain_of_mem_intSpanZeroAtOne hAconj hA hAA₀ hf
  have hspanIrr : ∀ f ∈ intSpanZeroAtOne (S : Set (↥L → ℂ)), f ∈ Submodule.span ℤ (Irr ↥L) :=
    fun f hf => Submodule.span_le.2 (fun g hg => mem_span_Irr_of_mem_indFamDetect (hmem g hg))
      (mem_intSpanZeroAtOne.1 hf).1
  refine ⟨blockMap h hW σ ω A₀ T, ?_, ?_, ?_, ?_⟩
  ·
    refine
      { isCharacter := fun χ hχ => isCharacter_of_mem_indFamDetect (hmem χ hχ)
        ne_zero := fun χ hχ => ne_zero_of_mem_indFamDetect (hmem χ hχ)
        star_mem := fun χ hχ => by
          rw [← Finset.mem_coe, hS]; exact star_mem_indFamDetect (hmem χ hχ)
        star_ne := fun χ hχ => star_ne_self_of_mem_indFamDetect_of_odd_natCard hodd (hmem χ hχ)
        charInner_eq_zero := fun χ hχ ψ hψ hne =>
          charInner_eq_zero_of_mem_indFamDetect (hmem χ hχ) (hmem ψ hψ) hne
        map_add := fun f _ g _ => dadeMapFun_add L A₀ T f g
        tau_mem := fun f hf => mem_virtualCharSpan_of_mem_span_Irr
          (dadeMapFun_mem_span_Irr hD (hdom f hf) (hspanIrr f hf))
        charInner_tau_tau := fun f hf g hg => by
          rw [charInner_eq_cfInner, charInner_eq_cfInner]
          exact cfInner_dadeMapFun hD (hdom f hf) (hdom g hg)
        tau_apply_one := fun f hf => dadeMapFun_apply_one_eq_zero hD (hdom f hf)
        R_subset := fun χ hχ r hr => mem_virtualCharSpan_of_mem_span_Irr
          (blockMap_subset_span_Irr hodd h hσ hAconj hA hAA₀ hD hW hω (hmem χ hχ) hr)
        charInner_R_self := fun χ hχ r hr => by
          rw [charInner_eq_cfInner]
          exact cfInner_blockMap_self hodd h hσ hAconj hA hAA₀ hD hW hω (hmem χ hχ) hr
        charInner_R_of_ne := fun χ hχ r hr s hs hrs => by
          rw [charInner_eq_cfInner]
          exact cfInner_blockMap_of_ne hodd h hσ hAconj hA hAA₀ hD hW hω (hmem χ hχ) hr hs hrs
        tau_sub_star := fun χ hχ =>
          dadeMapFun_sub_star_eq_sum_blockMap hodd h hσ hWH hAconj hA hA₀ hD hstab hdisj hω
            (hmem χ hχ)
        charInner_R_R := fun χ hχ ψ hψ h1 h2 r hr s hs => by
          rw [charInner_eq_cfInner]
          exact cfInner_blockMap_blockMap hodd h hσ hAconj hA hA₀ hD hW hω (hmem χ hχ)
            (hmem ψ hψ) h1 h2 hr hs }
  ·
    exact fun χ hχ => coe_blockMap_star hodd h hσ hAconj hA hAA₀ hD hW (hmem χ hχ)
  ·
    intro χ hχS hχIrr r hr i j
    rw [blockMap_irr h hσ hW hχIrr] at hr
    exact isOrthogonal_iff.2 (isOrthogonal_irrBlock_prodCharEta hodd h hAconj hA hA₀ hD hW hω
      (hmem χ hχS) hχIrr hr i j)
  ·
    intro j hj
    refine ⟨?_, ?_⟩
    · rw [← Finset.mem_coe, hS]
      exact primeTIrow_mem_indFamDetect h hσ hWH hj
    · rw [blockMap_row h hσ hW hj]
      exact coe_rowBlock h hW j

end Node

end PrimeDadeSubcoherence

end CFSG.FeitThompson
