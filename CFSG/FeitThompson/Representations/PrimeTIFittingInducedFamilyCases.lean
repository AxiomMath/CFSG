module

public import CFSG.FeitThompson.Representations.MinimalAbelianCoreBridgeCharacter
public import CFSG.FeitThompson.Representations.PrimeCubeLocalArrayNonlinearCharacters
public import CFSG.FeitThompson.Representations.PrimeComplementIrreducibleCases
public import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.FixedFreeQuotientUniformCoreDegrees
public import CFSG.FeitThompson.Representations.AbelianInertiaInducedBlock
public import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.PrimeTIDegreeSignCongruence
public import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
public import CFSG.FeitThompson.Representations.NonprincipalRowRestrictionsDetectCores
public import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
public import CFSG.FeitThompson.Representations.CentralFrobeniusFamilyDescription

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup ComplexOrder

section Detect

variable {L : Type*} [Group L] {F H K : Subgroup L}

theorem not_subset_charValueKernel_of_pos_cfInner_indClassFun [Fintype ↥K]
    (hFK : F ≤ K) {ψ : ↥F → ℂ} (hψ : ψ ∈ Irr ↥F)
    (hHψ : ¬ ((H.subgroupOf F : Set ↥F) ⊆ charValueKernel ψ)) {χ : ↥K → ℂ} (hχ : χ ∈ Irr ↥K)
    (hpos : 0 < cfInner (indClassFun (F.subgroupOf K)
      (ψ ∘ Subgroup.subgroupOfEquivOfLe hFK)) χ) :
    ¬ ((H.subgroupOf K : Set ↥K) ⊆ charValueKernel χ) := by
  intro hker
  have : Fintype ↥(F.subgroupOf K) := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hFK with he
  have hψ' : ψ ∘ e ∈ Irr ↥(F.subgroupOf K) := FrobeniusInduction.mem_Irr_comp_mulEquiv hψ e
  have hmem : ψ ∘ e ∈ resConstituents (F.subgroupOf K) χ := by
    refine mem_resConstituents.2 ⟨hψ', ?_⟩
    rwa [← cfInner_indClassFun_eq_cfInner_resClassFun hχ hψ']
  have hsub := FixedFreeCoreDegree.subset_charValueKernel_of_mem_resConstituents
    (Z := H.subgroupOf K) hχ hker hmem
  refine hHψ fun y hy => ?_
  have hyH : ((y : ↥F) : L) ∈ H := Subgroup.mem_subgroupOf.1 hy
  have hy' : e.symm y ∈ (H.subgroupOf K).subgroupOf (F.subgroupOf K) := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa [he] using hyH
  have hval := mem_charValueKernel.1 (hsub hy')
  simp only [Function.comp_apply, MulEquiv.apply_symm_apply, map_one] at hval
  exact mem_charValueKernel.2 hval

variable [Fintype L]

theorem indFamDetect_subgroupOf_subset_indFam :
    indFamDetect F (H.subgroupOf F) ⊆ indFam F (Irr ↥F) := by
  intro f hf
  rw [Irr_eq_irrChar]
  exact indFamDetect_subset_indFam_irrChar F (H.subgroupOf F) hf

omit [Fintype L] in
theorem exists_apply_ne_of_not_subset_charValueKernel {θ : ↥F → ℂ}
    (h : ¬ ((H.subgroupOf F : Set ↥F) ⊆ charValueKernel θ)) :
    ∃ x : ↥F, (x : L) ∈ H ∧ θ x ≠ θ 1 := by
  rw [Set.not_subset] at h
  obtain ⟨x, hxH, hx⟩ := h
  exact ⟨x, Subgroup.mem_subgroupOf.1 hxH, fun hc => hx (mem_charValueKernel.2 hc)⟩

theorem mem_indFamDetect_of_mem_Irr_of_not_subset {θ : ↥F → ℂ} (hθ : θ ∈ Irr ↥F)
    (hH : ¬ ((H.subgroupOf F : Set ↥F) ⊆ charValueKernel θ)) :
    indClassFun F θ ∈ indFamDetect F (H.subgroupOf F) := by
  refine (mem_indFamDetect_subgroupOf F).2
    ⟨θ, ?_, exists_apply_ne_of_not_subset_charValueKernel hH, rfl⟩
  rw [← Irr_eq_irrChar]
  exact hθ

end Detect

variable {L : Type*} [Group L] [Fintype L] {K W₁ W₂ H U : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

namespace IsMinimalAbelianCore

omit [Fintype L] in
theorem isMulCommutative_coreProduct (hc : IsMinimalAbelianCore K W₁ W₂ H U) :
    IsMulCommutative ↥(coreProduct H U) := by
  have := hc.normal
  have := hc.isMulCommutative_core
  have := hc.isMulCommutative_compl
  infer_instance

omit [Fintype L] in
theorem index_coreProduct [Finite L] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) :
    (coreProduct H U).index = Nat.card ↥W₁ * (coreCentralizer H U).relIndex U := by
  have hnormal := hc.normal
  have hF : Nat.card ↥(coreProduct H U) * (coreCentralizer H U).relIndex U = Nat.card ↥K := by
    rw [← hc.sup_eq]; exact card_coreProduct_mul_relIndex H U hc.inf_eq_bot
  have hKW : Nat.card ↥W₁ * Nat.card ↥K = Nat.card L := h.isComplement'_left.card_mul_card
  have hidx : (coreProduct H U).index * Nat.card ↥(coreProduct H U) = Nat.card L :=
    Subgroup.index_mul_card _
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(coreProduct H U))) ?_
  rw [hidx, ← hKW, ← hF]
  ring

theorem apply_one_of_mem_indFamDetect_coreProduct (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) {ζ : L → ℂ}
    (hζ : ζ ∈ indFamDetect (coreProduct H U) (H.subgroupOf (coreProduct H U))) :
    ζ 1 = (Nat.card ↥W₁ : ℂ) * ((coreCentralizer H U).relIndex U : ℂ) := by
  have habel := hc.isMulCommutative_coreProduct
  obtain ⟨ψ, hψ, -, rfl⟩ := (mem_indFamDetect_subgroupOf (coreProduct H U)).1 hζ
  rw [← Irr_eq_irrChar] at hψ
  rw [indClassFun_apply_one, Irr.apply_one_eq_one_of_isMulCommutative hψ, mul_one,
    index_coreProduct h hc]
  push_cast
  ring

theorem cfInner_eq_zero_of_mem_indFamDetect_coreProduct [(coreProduct H U).Normal] {ζ ξ : L → ℂ}
    (hζ : ζ ∈ indFamDetect (coreProduct H U) (H.subgroupOf (coreProduct H U)))
    (hξ : ξ ∈ indFamDetect (coreProduct H U) (H.subgroupOf (coreProduct H U)))
    (hne : ζ ≠ ξ) : cfInner ζ ξ = 0 :=
  NormalInducedFamily.cfInner_eq_zero_of_mem_indFam (coreProduct H U)
    (indFamDetect_subgroupOf_subset_indFam hζ) (indFamDetect_subgroupOf_subset_indFam hξ) hne

section Main

variable [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]

theorem primeTIrow_mem_indFamDetect (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIrow σ j ∈ indFamDetect K (H.subgroupOf K) := by
  refine (mem_indFamDetect_subgroupOf K).2
    ⟨h.primeTIres σ j, ?_, h.exists_mem_primeTIres_ne hσ hc.right_le hj,
      h.indClassFun_primeTIres hσ j⟩
  rw [← Irr_eq_irrChar]
  exact h.primeTIres_mem_Irr hσ j

theorem primeTIrow_mem_indFamDetect_coreProduct (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIrow σ j
      ∈ indFamDetect (coreProduct H U) (H.subgroupOf (coreProduct H U)) := by
  have : Fintype ↥K := Fintype.ofFinite _
  obtain ⟨ψ, hψIrr, hψ1, ⟨x, hxH, hx⟩, -, hrow⟩ := hc.exists_linearChar_primeTIres h hσ hj
  refine (mem_indFamDetect_subgroupOf (coreProduct H U)).2 ⟨ψ, ?_, ⟨x, hxH, ?_⟩, hrow.symm⟩
  · rw [← Irr_eq_irrChar]; exact hψIrr
  · rw [hψ1]; exact hx

theorem primeTIrow_one_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIrow σ j 1 = (Nat.card ↥W₁ : ℂ) * ((coreCentralizer H U).relIndex U : ℂ) := by
  rw [h.primeTIrow_one j, hc.primeTIres_one_eq_relIndex h hσ hj]

omit [Fintype ↑(Irr ↥W₁)] in
theorem exists_primeTISign_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) :
    ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧
      ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → h.primeTISign σ j = δ := by
  by_cases hex : ∃ j : Irr ↥W₂, j ≠ principalIrr ↥W₂
  · obtain ⟨j₀, hj₀⟩ := hex
    refine ⟨h.primeTISign σ j₀, h.primeTISign_eq_one_or_eq_neg_one j₀, fun j hj => ?_⟩
    refine h.primeTISign_eq_of_primeTIirr_one_eq hσ (principalIrr ↥W₁) j j₀ ?_
    rw [← h.primeTIres_one j, ← h.primeTIres_one j₀,
      hc.primeTIres_one_eq_relIndex h hσ hj, hc.primeTIres_one_eq_relIndex h hσ hj₀]
  · exact ⟨1, Or.inl rfl, fun j hj => absurd ⟨j, hj⟩ hex⟩

theorem indFamDetect_eq_union (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) :
    indFamDetect K (H.subgroupOf K)
      = (indFamDetect K (H.subgroupOf K) ∩ Irr L) ∪ primeTIrowFam h σ := by
  have hnormal := h.normal
  refine Set.Subset.antisymm (fun f hf => ?_)
    (Set.union_subset Set.inter_subset_left fun f hf => ?_)
  · obtain ⟨θ, hθ, ⟨x, hxH, hx⟩, rfl⟩ := (mem_indFamDetect_subgroupOf K).1 hf
    rw [← Irr_eq_irrChar] at hθ
    rcases h.exists_primeTIres_eq_or_indClassFun_mem_Irr hσ hc.prime_natCard hθ with
      ⟨j, hj, -⟩ | hirr
    · refine Or.inr (mem_primeTIrowFam.2 ⟨j, ?_, ?_⟩)
      · intro hj0
        rw [hj0, h.primeTIres_principal hσ] at hj
        rw [hj] at hx
        simp at hx
      · rw [← h.indClassFun_primeTIres hσ j, hj]
    · exact Or.inl ⟨hf, hirr⟩
  · obtain ⟨j, hj, rfl⟩ := mem_primeTIrowFam.1 hf
    exact primeTIrow_mem_indFamDetect h hc hσ hj

theorem disjoint_indFamDetect_inter_primeTIrowFam (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) :
    Disjoint (indFamDetect K (H.subgroupOf K) ∩ Irr L) (primeTIrowFam h σ) := by
  have hnormal := h.normal
  rw [Set.disjoint_left]
  intro f hf1 hf2
  obtain ⟨j, -, rfl⟩ := mem_primeTIrowFam.1 hf2
  exact h.indClassFun_primeTIres_notMem_Irr hσ hc.prime_natCard j
    (by rw [h.indClassFun_primeTIres hσ j]; exact hf1.2)

omit [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] in
theorem resClassFun_primeTIrow [Finite L] (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    resClassFun K (h.primeTIrow σ j) = (Nat.card ↥W₁ : ℂ) • h.primeTIres σ j := by
  have hcomm := h.isCyclicTIPair.isMulCommutative_left
  rw [h.primeTIrow_def j, resClassFun_sum,
    Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset ↑(Irr ↥W₁))) =>
      h.resClassFun_primeTIirr i j, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_Irr_eq_card_of_isMulCommutative,
    ← Nat.cast_smul_eq_nsmul ℂ]

theorem eq_primeTIrow_or_exists_sum_of_mem_indFamDetect_coreProduct
    [(coreProduct H U).Normal] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {ζ : L → ℂ} (hζ : ζ ∈ indFamDetect (coreProduct H U) (H.subgroupOf (coreProduct H U))) :
    (∃ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ ∧ ζ = h.primeTIrow σ j) ∨
      ∃ n : ↥(irrFinset ↥K) → ℕ,
        (∀ χ : ↥(irrFinset ↥K), n χ ≠ 0 →
          indClassFun K (χ : ↥K → ℂ) ∈ indFamDetect K (H.subgroupOf K) ∩ Irr L) ∧
        ζ = ∑ χ : ↥(irrFinset ↥K), (n χ : ℂ) • indClassFun K (χ : ↥K → ℂ) := by
  classical
  have hnormal := h.normal
  have hFK : coreProduct H U ≤ K := hc.coreProduct_le
  have : Fintype ↥((coreProduct H U).subgroupOf K) := Fintype.ofFinite _
  obtain ⟨ψ, hψ, hψH, rfl⟩ := (mem_indFamDetect_subgroupOf (coreProduct H U)).1 hζ
  rw [← Irr_eq_irrChar] at hψ
  set e := Subgroup.subgroupOfEquivOfLe hFK with he
  have hψ' : ψ ∘ e ∈ Irr ↥((coreProduct H U).subgroupOf K) :=
    FrobeniusInduction.mem_Irr_comp_mulEquiv hψ e
  set β := indClassFun ((coreProduct H U).subgroupOf K) (ψ ∘ e) with hβ
  obtain ⟨n, hn⟩ := exists_multiplicities_indClassFun hψ'
  have hζβ : indClassFun (coreProduct H U) ψ = indClassFun K β :=
    (AbelianInertiaBlock.indClassFun_indClassFun K hFK ψ).symm
  have hind : indClassFun (coreProduct H U) ψ
      = ∑ χ : ↥(irrFinset ↥K), (n χ : ℂ) • indClassFun K (χ : ↥K → ℂ) := by
    rw [hζβ, hβ, hn, AbelianInertiaBlock.indClassFun_sum K Finset.univ]
    exact Finset.sum_congr rfl fun χ _ => indClassFun_smul K _ _
  have hHψ : ¬ ((H.subgroupOf (coreProduct H U) : Set ↥(coreProduct H U))
      ⊆ charValueKernel ψ) := by
    obtain ⟨x, hxH, hx⟩ := hψH
    intro hsub
    exact hx (mem_charValueKernel.1 (hsub (Subgroup.mem_subgroupOf.2 hxH)))
  have hdet : ∀ χ : ↥(irrFinset ↥K), n χ ≠ 0 →
      ¬ ((H.subgroupOf K : Set ↥K) ⊆ charValueKernel (χ : ↥K → ℂ)) := by
    intro χ hχn
    refine not_subset_charValueKernel_of_pos_cfInner_indClassFun hFK hψ hHψ
      (mem_irrFinset.1 χ.2) ?_
    rw [← he, ← hβ, cfInner_eq_multiplicity hn χ]
    exact_mod_cast Nat.pos_of_ne_zero hχn
  by_cases hcase : ∃ (χ : ↥(irrFinset ↥K)) (j : Irr ↥W₂),
      n χ ≠ 0 ∧ (χ : ↥K → ℂ) = h.primeTIres σ j
  · obtain ⟨χ, j, hχn, hχj⟩ := hcase
    left
    have hj0 : j ≠ principalIrr ↥W₂ := by
      intro hj
      refine hdet χ hχn ?_
      rw [hχj, hj, h.primeTIres_principal hσ, charValueKernel_one]
      exact Set.subset_univ _
    refine ⟨j, hj0, ?_⟩
    have hMcf : h.primeTIrow σ j ∈ classFun L := by
      rw [← h.indClassFun_primeTIres hσ j]
      exact indClassFun_mem_classFun K _
    have hinner : cfInner (indClassFun (coreProduct H U) ψ) (h.primeTIrow σ j)
        = (Nat.card ↥W₁ : ℂ) * (n χ : ℂ) := by
      rw [hζβ, cfInner_indClassFun K β hMcf, resClassFun_primeTIrow h j, cfInner_smul_right]
      have hbc : cfInner β (h.primeTIres σ j) = (n χ : ℂ) := by
        rw [← hχj, hβ, cfInner_eq_multiplicity hn χ]
      rw [hbc]
      simp
    by_contra hne
    have hzero := cfInner_eq_zero_of_mem_indFamDetect_coreProduct hζ
      (primeTIrow_mem_indFamDetect_coreProduct h hc hσ hj0) hne
    rw [hinner] at hzero
    exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.card_pos (α := ↥W₁)).ne')
      (Nat.cast_ne_zero.2 hχn) hzero
  · right
    refine ⟨n, fun χ hχn => ⟨?_, ?_⟩, hind⟩
    · exact mem_indFamDetect_of_mem_Irr_of_not_subset (mem_irrFinset.1 χ.2) (hdet χ hχn)
    · refine h.indClassFun_mem_Irr_of_forall_ne hσ (mem_irrFinset.1 χ.2) fun j hj => ?_
      exact hcase ⟨χ, j, hχn, hj.symm⟩

omit [Fintype ↑(Irr ↥W₁)] in
theorem mem_span_indFamDetect_of_mem_indFamDetect_coreProduct [(coreProduct H U).Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hc : IsMinimalAbelianCore K W₁ W₂ H U)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : L → ℂ}
    (hζ : ζ ∈ indFamDetect (coreProduct H U) (H.subgroupOf (coreProduct H U))) :
    ζ ∈ Submodule.span ℤ (indFamDetect K (H.subgroupOf K)) := by
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  rcases eq_primeTIrow_or_exists_sum_of_mem_indFamDetect_coreProduct h hc hσ hζ with
    ⟨j, hj, rfl⟩ | ⟨n, hn, rfl⟩
  · exact Submodule.subset_span (primeTIrow_mem_indFamDetect h hc hσ hj)
  · refine Submodule.sum_mem _ fun χ _ => ?_
    by_cases hχn : n χ = 0
    · simp [hχn]
    · have hsmul : ((n χ : ℂ) • indClassFun K (χ : ↥K → ℂ))
          = (n χ : ℤ) • indClassFun K (χ : ↥K → ℂ) := by
        rw [← Int.cast_smul_eq_zsmul ℂ]
        push_cast
        ring_nf
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hn χ hχn).1)

end Main

end IsMinimalAbelianCore

end CFSG.FeitThompson
