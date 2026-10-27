module

public import CFSG.FeitThompson.Representations.CoreDetectingFamilyAntirealBlocks
public import CFSG.FeitThompson.Representations.InducedFamilyIrreducibleRowOrthogonal
public import CFSG.FeitThompson.Representations.CoreCoherentIrreducibleArrayOrthogonality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace IsPrimeCyclicTIHyp

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

theorem odd_natCard_sup (h : IsPrimeCyclicTIHyp K W₁ W₂) : Odd (Nat.card ↥(W₁ ⊔ W₂)) :=
  h.isCyclicTIPair.odd_natCard

variable [Finite ↥W₂]

theorem starIrr_ne_principalIrr_right (h : IsPrimeCyclicTIHyp K W₁ W₂) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : starIrr j ≠ principalIrr ↥W₂ :=
  starIrr_ne_principalIrr hj

theorem starIrr_ne_self_right (h : IsPrimeCyclicTIHyp K W₁ W₂) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : starIrr j ≠ j :=
  starIrr_ne_self h.isCyclicTIPair.odd_natCard_right hj

section Fintype

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]

theorem cfInner_primeTIrow_primeTIrow_of_ne (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j k : Irr ↥W₂} (hjk : j ≠ k) :
    cfInner (h.primeTIrow σ j) (h.primeTIrow σ k) = 0 := by
  classical
  rw [primeTIrow_def, primeTIrow_def, cfInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cfInner_sum_right]
  refine Finset.sum_eq_zero fun i' _ => ?_
  rw [h.cfInner_primeTIirr hσ, if_neg (by simp [hjk])]

theorem cfInner_self_primeTIrow_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    cfInner (h.primeTIrow σ j) (h.primeTIrow σ j) = (Nat.card ↥W₁ : ℂ) :=
  h.cfInner_self_primeTIrow hσ j

theorem cfInner_self_four_family (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j k : Irr ↥W₂) {ξ : L → ℂ} (hξ : ξ ∈ Irr L) :
    cfInner ξ ξ = 1 ∧ cfInner (star ξ) (star ξ) = 1 ∧
      cfInner (h.primeTIrow σ j) (h.primeTIrow σ j) = (Nat.card ↥W₁ : ℂ) ∧
      cfInner (h.primeTIrow σ k) (h.primeTIrow σ k) = (Nat.card ↥W₁ : ℂ) :=
  ⟨cfInner_self_of_mem_Irr hξ, cfInner_self_of_mem_Irr (star_mem_Irr hξ),
    h.cfInner_self_primeTIrow hσ j, h.cfInner_self_primeTIrow hσ k⟩

end Fintype

end IsPrimeCyclicTIHyp

theorem primeDade_four_family_antireal_blocks {G : Type*} [Group G] [Fintype G]
    {L : Subgroup G} [Fintype ↥L] {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)]
    {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
    {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
    {A₀ : Set G} {T : G → Subgroup G}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H)
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
    (hodd : Odd (Nat.card G))
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K)
    (hHθ : ∃ y : ↥K, (y : ↥L) ∈ H ∧ y ∉ charValueKernel θ)
    (hξ : indClassFun K θ ∈ Irr ↥L)
    (hdeg : indClassFun K θ 1 = h.primeTIrow σ j 1) :
    h.primeTISign σ (starIrr j) = h.primeTISign σ j ∧
    h.primeTIrow σ (starIrr j) = star (h.primeTIrow σ j) ∧
    (indClassFun K θ ≠ star (indClassFun K θ) ∧
      indClassFun K θ ≠ h.primeTIrow σ j ∧
      indClassFun K θ ≠ h.primeTIrow σ (starIrr j) ∧
      star (indClassFun K θ) ≠ h.primeTIrow σ j ∧
      star (indClassFun K θ) ≠ h.primeTIrow σ (starIrr j) ∧
      h.primeTIrow σ j ≠ h.primeTIrow σ (starIrr j)) ∧
    (cfInner (indClassFun K θ) (star (indClassFun K θ)) = 0 ∧
      cfInner (indClassFun K θ) (h.primeTIrow σ j) = 0 ∧
      cfInner (indClassFun K θ) (h.primeTIrow σ (starIrr j)) = 0 ∧
      cfInner (star (indClassFun K θ)) (h.primeTIrow σ j) = 0 ∧
      cfInner (star (indClassFun K θ)) (h.primeTIrow σ (starIrr j)) = 0 ∧
      cfInner (h.primeTIrow σ j) (h.primeTIrow σ (starIrr j)) = 0) ∧
    (∃ d : ℕ, 0 < d ∧ indClassFun K θ 1 = (d : ℂ) ∧ star (indClassFun K θ) 1 = (d : ℂ) ∧
      h.primeTIrow σ j 1 = (d : ℂ) ∧ h.primeTIrow σ (starIrr j) 1 = (d : ℂ)) ∧
    (cfInner (indClassFun K θ) (indClassFun K θ) = 1 ∧
      cfInner (star (indClassFun K θ)) (star (indClassFun K θ)) = 1 ∧
      cfInner (h.primeTIrow σ j) (h.primeTIrow σ j) = (Nat.card ↥W₁ : ℂ) ∧
      cfInner (h.primeTIrow σ (starIrr j)) (h.primeTIrow σ (starIrr j)) = (Nat.card ↥W₁ : ℂ)) ∧
    (∀ x : ↥L, x ∉ A ∪ {1} → indClassFun K θ x = 0 ∧ star (indClassFun K θ) x = 0 ∧
      h.primeTIrow σ j x = 0 ∧ h.primeTIrow σ (starIrr j) x = 0) ∧
    (∀ f ∈ Submodule.span ℤ ({indClassFun K θ, star (indClassFun K θ), h.primeTIrow σ j,
        h.primeTIrow σ (starIrr j)} : Set (↥L → ℂ)), f 1 = 0 → f ∈ dadeDomain L A₀) ∧
    (∃ ρ ∈ Irr G, star ρ ≠ ρ ∧
      dadeMapFun L A₀ T (indClassFun K θ - star (indClassFun K θ)) = ρ - star ρ ∧
      (∀ (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)),
        cfInner ρ ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω a b) = 0 ∧
          cfInner (star ρ)
            ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω a b) = 0) ∧
      ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype),
        ρ v = 0) ∧
    dadeMapFun L A₀ T (h.primeTIrow σ j - h.primeTIrow σ (starIrr j))
      = h.primeTISign σ j • ∑ i : ↑(Irr ↥W₁),
          ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω (irrMapSubtype L W₁ i)
              (irrMapSubtype L W₂ j)
            - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω (irrMapSubtype L W₁ i)
              (irrMapSubtype L W₂ (starIrr j))) := by
  classical
  have hKn : K.Normal := h.normal
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  set ξ : ↥L → ℂ := indClassFun K θ with hξdef
  have hjs : starIrr j ≠ principalIrr ↥W₂ := h.starIrr_ne_principalIrr_right hj
  have hjsne : starIrr j ≠ j := h.starIrr_ne_self_right hj
  have hLodd : Odd (Nat.card ↥L) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  obtain ⟨y, hyH, hy⟩ := hHθ
  have hmemS : ξ ∈ indFamDetect K (H.subgroupOf K) := by
    refine (mem_indFamDetect_subgroupOf K).2 ⟨θ, ?_, ⟨y, hyH, ?_⟩, rfl⟩
    · rw [← Irr_eq_irrChar]; exact hθ
    · intro hc; exact hy (mem_charValueKernel.2 hc)
  have hsign : h.primeTISign σ (starIrr j) = h.primeTISign σ j := h.primeTISign_starIrr_eq hσ j
  have hrow : h.primeTIrow σ (starIrr j) = star (h.primeTIrow σ j) :=
    h.primeTIrow_starIrr_eq_star hσ j
  have hm1 : (Nat.card ↥W₁ : ℂ) ≠ 1 := by
    intro hc
    have hc' : Nat.card ↥W₁ = 1 := by exact_mod_cast hc
    exact h.left_ne_bot (Subgroup.card_eq_one.1 hc')
  have hm0 : (Nat.card ↥W₁ : ℂ) ≠ 0 := by simp
  have hnormξ : cfInner ξ ξ = 1 := cfInner_self_of_mem_Irr hξ
  have hnormsξ : cfInner (star ξ) (star ξ) = 1 := cfInner_self_of_mem_Irr (star_mem_Irr hξ)
  have hnormj : cfInner (h.primeTIrow σ j) (h.primeTIrow σ j) = (Nat.card ↥W₁ : ℂ) :=
    h.cfInner_self_primeTIrow_eq hσ j
  have hnormk : cfInner (h.primeTIrow σ (starIrr j)) (h.primeTIrow σ (starIrr j))
      = (Nat.card ↥W₁ : ℂ) := h.cfInner_self_primeTIrow_eq hσ (starIrr j)
  have horthjk : cfInner (h.primeTIrow σ j) (h.primeTIrow σ (starIrr j)) = 0 :=
    h.cfInner_primeTIrow_primeTIrow_of_ne hσ (Ne.symm hjsne)
  have hξind : ξ ∈ indFam K (Irr ↥K) := indClassFun_mem_indFam K hθ
  have hsξind : star ξ ∈ indFam K (Irr ↥K) := by
    rw [hξdef, ← DisjointCoherentFamilies.indClassFun_star]
    exact indClassFun_mem_indFam K (star_mem_Irr hθ)
  have ho1 : cfInner ξ (h.primeTIrow σ j) = 0 :=
    h.cfInner_primeTIrow_eq_zero_of_mem_indFam hσ hξind hξ j
  have ho2 : cfInner ξ (h.primeTIrow σ (starIrr j)) = 0 :=
    h.cfInner_primeTIrow_eq_zero_of_mem_indFam hσ hξind hξ (starIrr j)
  have ho3 : cfInner (star ξ) (h.primeTIrow σ j) = 0 :=
    h.cfInner_primeTIrow_eq_zero_of_mem_indFam hσ hsξind (star_mem_Irr hξ) j
  have ho4 : cfInner (star ξ) (h.primeTIrow σ (starIrr j)) = 0 :=
    h.cfInner_primeTIrow_eq_zero_of_mem_indFam hσ hsξind (star_mem_Irr hξ) (starIrr j)
  have hne1 : ξ ≠ 1 := ne_one_of_mem_indFamDetect hmemS
  have hnr : ξ ≠ star ξ := by
    rw [star_eq_conj_fun]
    exact ne_conj_of_mem_Irr_of_ne_one_of_odd hLodd hξ hne1
  have hdistinct : ξ ≠ star ξ ∧ ξ ≠ h.primeTIrow σ j ∧ ξ ≠ h.primeTIrow σ (starIrr j) ∧
      star ξ ≠ h.primeTIrow σ j ∧ star ξ ≠ h.primeTIrow σ (starIrr j) ∧
      h.primeTIrow σ j ≠ h.primeTIrow σ (starIrr j) := by
    refine ⟨hnr, ?_, ?_, ?_, ?_, ?_⟩
    · intro hc; rw [hc, hnormj] at hnormξ; exact hm1 hnormξ
    · intro hc; rw [hc, hnormk] at hnormξ; exact hm1 hnormξ
    · intro hc; rw [hc, hnormj] at hnormsξ; exact hm1 hnormsξ
    · intro hc; rw [hc, hnormk] at hnormsξ; exact hm1 hnormsξ
    · intro hc; rw [hc, hnormk] at horthjk; exact hm0 horthjk
  have horth : cfInner ξ (star ξ) = 0 ∧ cfInner ξ (h.primeTIrow σ j) = 0 ∧
      cfInner ξ (h.primeTIrow σ (starIrr j)) = 0 ∧ cfInner (star ξ) (h.primeTIrow σ j) = 0 ∧
      cfInner (star ξ) (h.primeTIrow σ (starIrr j)) = 0 ∧
      cfInner (h.primeTIrow σ j) (h.primeTIrow σ (starIrr j)) = 0 :=
    ⟨cfInner_eq_zero_of_mem_Irr hξ (star_mem_Irr hξ) hnr, ho1, ho2, ho3, ho4, horthjk⟩
  have hdegs : ∃ d : ℕ, 0 < d ∧ ξ 1 = (d : ℂ) ∧ star ξ 1 = (d : ℂ) ∧
      h.primeTIrow σ j 1 = (d : ℂ) ∧ h.primeTIrow σ (starIrr j) 1 = (d : ℂ) := by
    obtain ⟨d, hd, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hξ
    refine ⟨d, hd, hd1, ?_, by rw [← hdeg, hd1], ?_⟩
    · rw [Pi.star_apply, RCLike.star_def, conj_apply_one_of_mem_Irr hξ, hd1]
    · rw [hrow, Pi.star_apply, RCLike.star_def, ← hdeg, hd1, map_natCast]
  have hsupp : ∀ x : ↥L, x ∉ A ∪ {1} → ξ x = 0 ∧ star ξ x = 0 ∧
      h.primeTIrow σ j x = 0 ∧ h.primeTIrow σ (starIrr j) x = 0 := by
    intro x hx
    have h1 : ξ x = 0 :=
      PrimeDadeSubcoherence.apply_eq_zero_of_mem_indFamDetect_of_notMem hAconj hA hmemS hx
    refine ⟨h1, by simp [Pi.star_apply, h1], h.primeTIrow_eq_zero hσ hWH hAconj hA hj hx,
      h.primeTIrow_eq_zero hσ hWH hAconj hA hjs hx⟩
  have hgenIrr : ({ξ, star ξ, h.primeTIrow σ j, h.primeTIrow σ (starIrr j)} : Set (↥L → ℂ))
      ⊆ (Submodule.span ℤ (Irr ↥L) : Set (↥L → ℂ)) := by
    rintro g (rfl | rfl | rfl | rfl)
    · exact Submodule.subset_span hξ
    · exact Submodule.subset_span (star_mem_Irr hξ)
    · exact virtualChars_le_span_Irr (primeTIrow_mem_virtualChars h hσ j)
    · exact virtualChars_le_span_Irr (primeTIrow_mem_virtualChars h hσ (starIrr j))
  have hdomain : ∀ f ∈ Submodule.span ℤ ({ξ, star ξ, h.primeTIrow σ j,
      h.primeTIrow σ (starIrr j)} : Set (↥L → ℂ)), f 1 = 0 → f ∈ dadeDomain L A₀ := by
    intro f hf hf1
    refine mem_dadeDomain_of_mem_span_Irr (Submodule.span_le.2 hgenIrr hf) ?_
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact hf1
    · refine eq_zero_of_mem_span_of_forall_eq_zero (fun s hs => ?_) hf
      have hxA : x ∉ A ∪ {1} := by
        intro hc
        rcases hc with hc | hc
        · exact hx (hA₀ ⟨x, subset_bridgeSupport_left hc, rfl⟩)
        · exact hx1 hc
      obtain ⟨h1, h2, h3, h4⟩ := hsupp x hxA
      rcases hs with rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
  have hpairsub : ({ξ, star ξ} : Set (↥L → ℂ))
      ⊆ ({ξ, star ξ, h.primeTIrow σ j, h.primeTIrow σ (starIrr j)} : Set (↥L → ℂ)) := by
    rintro g (rfl | rfl)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hpairdom : ∀ f ∈ charSpanZero ({ξ, star ξ} : Set (↥L → ℂ)), f ∈ dadeDomain L A₀ := by
    intro f hf
    obtain ⟨hspan, h1⟩ := mem_charSpanZero.1 hf
    exact hdomain f (Submodule.span_mono hpairsub hspan) h1
  obtain ⟨ρ, hρ, hρnr, hρeq⟩ := exists_dadeMapFun_sub_star_eq hD hξ hnr hpairdom
  have hdomsub : ξ - star ξ ∈ dadeDomain L A₀ := by
    refine hdomain _ (Submodule.sub_mem _ (Submodule.subset_span (Set.mem_insert _ _))
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) ?_
    simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def, conj_apply_one_of_mem_Irr hξ]
    ring
  have hvan : ∀ v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype), (ρ - star ρ) v = 0 := by
    intro v hv
    rw [← hρeq]
    rw [← image_cyclicTIset_eq] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    have hxA : (x : G) ∈ A₀ := hA₀ ⟨x,
      cyclicTIsetConj_subset_bridgeSupport (cyclicTIset_subset_cyclicTIsetConj _ _ hx), rfl⟩
    have hxK : x ∉ K := h.notMem_of_mem_cyclicTIset hx
    have h0 : ξ x = 0 := indClassFun_eq_zero_of_notMem K θ hxK
    rw [← coe_dadeMap hD ⟨_, hdomsub⟩, dadeMap_apply_mem hD ⟨_, hdomsub⟩ hxA]
    have hx' : (⟨(x : G), hD.mem_of_mem hxA⟩ : ↥L) = x := Subtype.ext rfl
    simp only [hx', Pi.sub_apply, Pi.star_apply, h0]
    simp
  have horthρ : ∀ (a : Irr ↥(W₁.map L.subtype)) (b : Irr ↥(W₂.map L.subtype)),
      cfInner ρ (hW.prodCharEta ω a b) = 0 ∧ cfInner (star ρ) (hW.prodCharEta ω a b) = 0 := by
    intro a b
    have hχ : ((hW.basisProdIrr (a, b) : classFun ↥((W₁ ⊔ W₂).map L.subtype)) :
        ↥((W₁ ⊔ W₂).map L.subtype) → ℂ) ∈ Irr ↥((W₁ ⊔ W₂).map L.subtype) := by
      rw [hW.coe_basisProdIrr_apply]
      exact hW.prodChar_mem_Irr a.2 b.2
    have h1 : IsOrthogonal ρ (hW.prodCharEta ω a b) := by
      have hsi : ρ ∈ signedIrr G := Irr_subset_signedIrr hρ
      have hne : ρ ≠ fun x => (starRingEnd ℂ) (ρ x) := by
        rw [← star_eq_conj_fun]
        exact fun hc => hρnr hc.symm
      have hz : ∀ x ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
          (W₂.map L.subtype), (ρ - fun z => (starRingEnd ℂ) (ρ z)) x = 0 := by
        intro x hx
        simpa [star_eq_conj_fun] using hvan x hx
      have hres := hW.isOrthogonal_apply_of_ne_conj hω hsi hne hz hχ
      rwa [← hW.prodCharEta_eq_coe_apply] at hres
    have h2 : IsOrthogonal (star ρ) (hW.prodCharEta ω a b) := by
      have hsi : star ρ ∈ signedIrr G := Irr_subset_signedIrr (star_mem_Irr hρ)
      have hne : star ρ ≠ fun x => (starRingEnd ℂ) (star ρ x) := by
        rw [← star_eq_conj_fun, star_star]
        exact hρnr
      have hz : ∀ x ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
          (W₂.map L.subtype), (star ρ - fun z => (starRingEnd ℂ) (star ρ z)) x = 0 := by
        intro x hx
        have hx0 := hvan x hx
        simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def, starRingEnd_self_apply] at hx0 ⊢
        linear_combination -hx0
      have hres := hW.isOrthogonal_apply_of_ne_conj hω hsi hne hz hχ
      rwa [← hW.prodCharEta_eq_coe_apply] at hres
    exact ⟨isOrthogonal_iff.1 h1, isOrthogonal_iff.1 h2⟩
  have hone : ∀ i : Irr ↥W₁, h.primeTIirr σ i j 1 = h.primeTIirr σ i (starIrr j) 1 :=
    fun i => h.primeTIirr_one_starIrr_eq hσ i j
  have htransfer : dadeMapFun L A₀ T (h.primeTIrow σ j - h.primeTIrow σ (starIrr j))
      = h.primeTISign σ j • ∑ i : ↑(Irr ↥W₁),
          (hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
            - hW.prodCharEta ω (irrMapSubtype L W₁ i)
              (irrMapSubtype L W₂ (starIrr j))) := by
    have hsplit : h.primeTIrow σ j - h.primeTIrow σ (starIrr j)
        = ∑ i : ↑(Irr ↥W₁), (h.primeTIirr σ i j - h.primeTIirr σ i (starIrr j)) := by
      rw [IsPrimeCyclicTIHyp.primeTIrow_def, IsPrimeCyclicTIHyp.primeTIrow_def,
        ← Finset.sum_sub_distrib]
    rw [hsplit, dadeMapFun_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmem := h.primeTIirr_sub_mem_dadeDomain hσ hWH hA hA₀ i hj hjs (hone i)
    rw [← coe_dadeMap hD ⟨_, hmem⟩]
    exact h.dadeMap_primeTIirr_sub_eq hσ hWH hA hA₀ hD hstab hdisj hω i hj hjs (hone i)
  exact ⟨hsign, hrow, hdistinct, horth, hdegs, ⟨hnormξ, hnormsξ, hnormj, hnormk⟩, hsupp, hdomain,
    ⟨ρ, hρ, hρnr, hρeq, horthρ, fun v hv =>
      apply_eq_zero_of_forall_prodCharEta hW hω (Irr_subset_classFun hρ)
        (fun i k => (horthρ i k).1) hv⟩, htransfer⟩

end CFSG.FeitThompson
