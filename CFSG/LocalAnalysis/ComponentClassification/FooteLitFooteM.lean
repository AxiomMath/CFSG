module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma45

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isFooteM_conjugate (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) (g : G) :
    IsFooteM L (conjugate M g) := by
  obtain ⟨z, A, E, hAmax, hAF, hE2, hE8, hEA, rfl⟩ := hM
  refine ⟨g⁻¹ * z * g, conjugate A g, conjugate E g, hAmax.conjugate g,
    conjugate_mem_footeFamilyOf hAF g, sq_eq_one_of_mem_conjugate hE2 g,
    by rw [card_conjugate_eq_card, hE8], fun x hx => ?_, (footeME_conjugate h.huniq E g).symm⟩
  rw [mem_conjugate_iff] at hx
  exact mem_coreActionKernel_conjugate (hEA hx)

theorem IsFooteM.exists_card_eight (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ∃ E : Subgroup G, (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 8 ∧ E ≤ coreActionKernel M := by
  obtain ⟨z, A, E, hAmax, hAF, hE2, hE8, hEA, rfl⟩ := hM
  obtain ⟨-, S, -, -, -, -, hS, -, hES, -⟩ := foote_lemma_4_5_sylow h hAmax hAF hE2 hE8 hEA
  exact ⟨E, hE2, hE8, hES.trans hS.le⟩

theorem IsFooteM.exists_footeF (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ∃ e : G, FootePointedMaximal e (footeF L e) ∧ footeF L e ∈ footeFamilyOf L ∧
      footeF L e ≤ M ∧ footeF L e ⊔ oddCoreIn M = M := by
  obtain ⟨e, -, -, -, hKmax, hKF, -, -, hKM, hsup, -, -⟩ := hM.sylow h
  exact ⟨e, hKmax, hKF, hKM, hsup⟩

theorem IsFooteM.exists_iSup (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ∃ E : Subgroup G, M = ⨆ e ∈ E, ⨆ (_ : e ≠ 1), footeF L e ∧
      ∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (footeF L e) := by
  obtain ⟨z, A, E, hAmax, hAF, hE2, hE8, hEA, rfl⟩ := hM
  have hspec := footeME_spec h hAmax hAF (isMulCommutative_of_sq_eq_one hE2) hE2 hE8 hEA
  exact ⟨E, rfl, fun e he he1 => (hspec.1 e he he1).1⟩

theorem IsFooteM.commutator_eq (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ⁅M, M⁆ = M := by
  obtain ⟨E, hME, hK⟩ := hM.exists_iSup h
  refine le_antisymm ((Subgroup.commutator_le).mpr fun x hx y hy => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  conv_lhs => rw [hME]
  refine iSup₂_le fun e he => iSup_le fun he1 => ?_
  have hKM : footeF L e ≤ M := hME ▸ footeF_le_footeME he he1
  rw [← GSThmB.commutator_eq_self_of_isPComponent (hK e he he1).2.1 (hK e he he1).2.2]
  exact commutator_mono hKM hKM

theorem IsFooteM.le_oddResidualIn (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    M ≤ oddResidualIn M := by
  obtain ⟨E, hME, hK⟩ := hM.exists_iSup h
  conv_lhs => rw [hME]
  refine iSup₂_le fun e he => iSup_le fun he1 => ?_
  have hKM : footeF L e ≤ M := hME ▸ footeF_le_footeME he he1
  exact (oddResidualIn_eq_self_of_isPComponent (hK e he he1).2.1 (hK e he he1).2.2).ge.trans
    (oddResidualIn_mono hKM)

theorem IsFooteM.quotient (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    IsSimpleGroup (M ⧸ pPrimeCore 2 M) ∧
      Nonempty (M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) := by
  obtain ⟨e, hKmax, hKF, hKM, hsup⟩ := hM.exists_footeF h
  obtain ⟨-, e₁, -⟩ := restriction_quotient_mulEquiv hKM hsup
  obtain ⟨hs, ⟨e₂⟩⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf h.hGA h.hGC h.hSA
    h.footeFamilyType h.hrank2 hKmax.1 hKF
  have := hs
  exact ⟨e₁.symm.isSimpleGroup, ⟨e₁.symm.trans e₂⟩⟩

theorem IsFooteM.exists_mul_ne (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ∃ a b : M ⧸ pPrimeCore 2 M, a * b ≠ b * a := by
  obtain ⟨hs, -⟩ := hM.quotient h
  by_contra hall
  push Not at hall
  set Q := M ⧸ pPrimeCore 2 M with hQ
  have h1 : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hM.commutator_eq h
  have hperf : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := by
    have h2 := congrArg (map (QuotientGroup.mk' (pPrimeCore 2 M))) h1
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      QuotientGroup.range_mk'] at h2
  have hbot : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x _ y _
    exact hall y x
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  have ha : a ∈ (⊤ : Subgroup Q) := mem_top a
  have hb : b ∈ (⊤ : Subgroup Q) := mem_top b
  rw [← hperf, hbot, mem_bot] at ha hb
  rw [ha, hb]

theorem IsFooteM.le_or_le (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    {N : Subgroup G} (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G)) :
    N ≤ oddCoreIn M ∨ M ≤ N ⊔ oddCoreIn M := by
  obtain ⟨hs, -⟩ := hM.quotient h
  have hn : (N.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  set π := QuotientGroup.mk' (pPrimeCore 2 M) with hπ
  have hn' : ((N.subgroupOf M).map π).Normal := hn.map π (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hn' with h1 | h1
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    intro x hx
    exact ⟨⟨x, hNM hx⟩, h1 hx, rfl⟩
  · right
    intro x hx
    have h2 : π ⟨x, hx⟩ ∈ (N.subgroupOf M).map π := h1 ▸ mem_top _
    obtain ⟨⟨y, hyM⟩, hyN, hyx⟩ := mem_map.mp h2
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    have h3 : x = y * (y⁻¹ * x) := by group
    rw [h3]
    refine mul_mem (mem_sup_left hyN) (mem_sup_right ⟨_, hyx, ?_⟩)
    simp

theorem IsFooteM.inf_coreActionKernel_le (h : FooteSec4 G L) {M : Subgroup G}
    (hM : IsFooteM L M) : M ⊓ coreActionKernel M ≤ oddCoreIn M := by
  obtain ⟨hs, -⟩ := hM.quotient h
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (hM.exists_mul_ne h)).2
  intro x hx
  exact mem_oddCoreIn_of_mem_coreActionKernel hZ (mem_inf.mp hx).1 (mem_inf.mp hx).2

theorem IsFooteM.exists_isKleinFour (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ∃ W : Subgroup G, IsKleinFour W ∧ W ≤ M := by
  obtain ⟨e, -, hKF, hKM, -⟩ := hM.exists_footeF h
  have hrank : CFSG.Open.pRank 2 (footeF L e) = 2 := by
    have h1 := h.hrank2 _ hKF
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h1
  obtain ⟨V, hVK, hVel, hVcard⟩ := SectionRank.exists_pRank one_lt_two (footeF L e)
  rw [hrank] at hVcard
  exact ⟨V, isKleinFour_of_card_eq_four (by rw [hVcard]; norm_num) hVel.2, hVK.trans hKM⟩

theorem IsFooteM.not_odd (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) :
    ¬ Odd (Nat.card M) := by
  obtain ⟨W, hW, hWM⟩ := hM.exists_isKleinFour h
  intro hodd
  have h1 := card_dvd_of_le hWM
  rw [hW.card_four] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h1))

end CFSG.ComponentClassification.FooteLit
