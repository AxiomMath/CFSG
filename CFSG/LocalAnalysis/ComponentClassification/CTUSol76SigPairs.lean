module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigFinal

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

omit [Finite G] in
theorem mk_mem_center_quot_of_mem_coreActionKernel {K : Subgroup G} {y : ↥K}
    (hy : (y : G) ∈ coreActionKernel K) :
    QuotientGroup.mk' (pPrimeCore 2 ↥K) y ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
  rw [mem_center_iff]
  intro z
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) z
  exact (mk_mul_comm_iff (N := K) k y).mpr (hy.2 k k.2)

theorem orderOf_mk_eq_two {K : Subgroup G} {y : ↥K} (hy2 : orderOf y = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥K) y) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy : y ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2] at h
  refine orderOf_eq_prime (by rw [← map_pow, hy, map_one]) ?_
  intro h1
  have hO : y ∈ pPrimeCore 2 ↥K := by rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
  have h := orderOf_dvd_natCard (⟨y, hO⟩ : pPrimeCore 2 ↥K)
  rw [Subgroup.orderOf_mk, hy2] at h
  exact absurd (Nat.Coprime.eq_one_of_dvd (pPrimeCore_coprime_card (p := 2) (G := ↥K)) h)
    (by norm_num)

theorem exists_orderOf_eq_two_mk_eq {K : Subgroup G} {x : ↥K ⧸ pPrimeCore 2 ↥K}
    (hx2 : orderOf x = 2) :
    ∃ w : ↥K, orderOf w = 2 ∧ QuotientGroup.mk' (pPrimeCore 2 ↥K) w = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) x
  have hx' : (QuotientGroup.mk' (pPrimeCore 2 ↥K) k) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (QuotientGroup.mk' (pPrimeCore 2 ↥K) k)
    rwa [hx2] at h
  have hk2 : k ^ 2 ∈ pPrimeCore 2 ↥K := by
    have h : QuotientGroup.mk' (pPrimeCore 2 ↥K) (k ^ 2) = 1 := by rw [map_pow, hx']
    rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h
  have hodd : Odd (orderOf (k ^ 2)) := by
    have hdvd := orderOf_dvd_natCard (⟨k ^ 2, hk2⟩ : pPrimeCore 2 ↥K)
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K)))
      hdvd
  obtain ⟨c, hc⟩ := hodd
  have himg : QuotientGroup.mk' (pPrimeCore 2 ↥K) (k ^ orderOf (k ^ 2)) =
      QuotientGroup.mk' (pPrimeCore 2 ↥K) k := by
    rw [map_pow, hc, pow_succ, pow_mul, hx', one_pow, one_mul]
  refine ⟨k ^ orderOf (k ^ 2), orderOf_eq_prime ?_ ?_, himg⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
  · intro h1
    rw [h1, map_one] at himg
    rw [← himg, orderOf_one] at hx2
    norm_num at hx2

theorem exists_orderOf_eq_two_not_mem_coreActionKernel (hq : QuasisimpleTwoPartInput)
    (hG : SimpleAmbient G) {X K : Subgroup G} (hKX : IsTwoComponentIn K X)
    (hK : K ∈ solomonKStar G) {Y : Subgroup G} (hYK : Y ≤ K) (hY : Y ⊔ oddCoreIn K = K) :
    ∃ y ∈ Y, orderOf y = 2 ∧ y ∉ coreActionKernel K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have hQq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    isQuasisimple_quotient_of_isPComponent hKX.1 hKX.2
  have hcat := catalog_coreQuotient_of_mem_solomonKStar (kStarKProper_of_simpleAmbient hG) hKX hK
  have hrank : 2 ≤ CFSG.Open.pRank 2 Y :=
    (two_le_pRank_of_mem_solomonKStar hK).trans (pRank_le_of_sup_oddCoreIn hYK hY)
  obtain ⟨a, haY, ha2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hrank)
  obtain ⟨F, hFY, hF, haF⟩ := exists_isKleinFour_mem hrank haY ha2
  obtain ⟨b, hbF, hb1, hba⟩ : ∃ b ∈ F, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (F : Set G) ⊆ {1, a} := fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (h x hx hx1)
    have h2 : (F : Set G).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    have h3 : Nat.card F = (F : Set G).ncard := Nat.card_coe_set_eq _
    have h4 := hF.card_four
    omega
  have hb2 : orderOf b = 2 := orderOf_eq_two_of_isKleinFour hF hbF hb1
  have hbY : b ∈ Y := hFY hbF
  by_cases haQ : a ∈ coreActionKernel K
  swap
  · exact ⟨a, haY, ha2, haQ⟩
  by_cases hbQ : b ∈ coreActionKernel K
  swap
  · exact ⟨b, hbY, hb2, hbQ⟩
  set a' : ↥K := ⟨a, hYK haY⟩ with ha'
  set b' : ↥K := ⟨b, hYK hbY⟩ with hb'
  have ha'2 : orderOf a' = 2 := by rw [ha', Subgroup.orderOf_mk]; exact ha2
  have hb'2 : orderOf b' = 2 := by rw [hb', Subgroup.orderOf_mk]; exact hb2
  have huv : π a' ≠ π b' := by
    intro h
    have hab1 : a⁻¹ * b ≠ 1 := fun h1 => hba (inv_mul_eq_one.mp h1).symm
    have habF : a⁻¹ * b ∈ F := F.mul_mem (F.inv_mem haF) hbF
    have hc2 : orderOf (a'⁻¹ * b') = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_two_of_isKleinFour hF habF hab1
    have h2 := orderOf_mk_eq_two (K := K) hc2
    rw [map_mul, map_inv, ← hπ, h, inv_mul_cancel, orderOf_one] at h2
    norm_num at h2
  obtain ⟨x, hx2, hxZ⟩ := hq.1 _ hQq hcat (π a') (π b') (orderOf_mk_eq_two ha'2)
    (orderOf_mk_eq_two hb'2) huv (mk_mem_center_quot_of_mem_coreActionKernel haQ)
    (mk_mem_center_quot_of_mem_coreActionKernel hbQ)
  obtain ⟨w, hw2, hwx⟩ := exists_orderOf_eq_two_mk_eq hx2
  have hw2' : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw2
  obtain ⟨m, hmK, hmY⟩ := exists_conj_mem_of_sup_oddCoreIn hYK hY w.2 hw2'
  refine ⟨m⁻¹ * w * m, hmY, by rw [orderOf_inv_mul_mul, hw2'], fun hQ => hxZ ?_⟩
  set m' : ↥K := ⟨m, hmK⟩ with hm'
  have e : (⟨m⁻¹ * w * m, hYK hmY⟩ : ↥K) = m'⁻¹ * w * m' := Subtype.ext (by simp [hm'])
  have hc : (π m')⁻¹ * x * π m' ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    have h := mk_mem_center_quot_of_mem_coreActionKernel (K := K) (y := ⟨m⁻¹ * w * m, hYK hmY⟩) hQ
    rwa [e, map_mul, map_mul, map_inv, ← hπ, hwx] at h
  have h := (inferInstance : (center (↥K ⧸ pPrimeCore 2 ↥K)).Normal).conj_mem _ hc (π m')
  have e2 : π m' * ((π m')⁻¹ * x * π m') * (π m')⁻¹ = x := by group
  rwa [e2] at h

theorem exists_sigPair_of_third (hq : QuasisimpleTwoPartInput) (hG : SimpleAmbient G)
    {K K' K'' : Subgroup G} (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hK'' : K'' ∈ kStarComponents N) (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K')
    {e f : G} (heK : e ∈ K) (he2 : orderOf e = 2) (hfK' : f ∈ K') (hf2 : orderOf f = 2)
    (hfe : f * e = e * f) :
    ∃ V B : Subgroup G, SigPair N K K' V B ∧ f ∈ V ∧ e ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he2' : IsPGroup 2 (zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he2, pow_one])
  have heQ : zpowers e ≤ coreActionKernel K' :=
    zpowers_le.mpr (mem_coreActionKernel_of_ne hK hK' hne heK)
  have hrank' := two_le_pRank_inf_centralizer hK' he2' heQ
  have hfY : f ∈ K' ⊓ centralizer ((zpowers e : Subgroup G) : Set G) := by
    refine mem_inf.mpr ⟨hfK', ?_⟩
    rw [centralizer_zpowers_eq]
    exact mem_centralizer_singleton_iff.mpr hfe
  obtain ⟨V, hVY, hV, hfV⟩ := exists_isKleinFour_mem hrank' hfY hf2
  have hVK' : V ≤ K' := hVY.trans inf_le_left
  have hVe : V ≤ centralizer ({e} : Set G) := by
    have h := hVY.trans inf_le_right
    rwa [centralizer_zpowers_eq] at h
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hrank := two_le_pRank_inf_centralizer hK hV2 hVQ
  have heY : e ∈ K ⊓ centralizer (V : Set G) := mem_inf.mpr ⟨heK, mem_centralizer_iff.mpr
    fun v hv => (mem_centralizer_singleton_iff.mp (hVe hv))⟩
  obtain ⟨F, hFY, hF, heF⟩ := exists_isKleinFour_mem hrank heY he2
  have hFK : F ≤ K := hFY.trans inf_le_left
  have hFV : F ≤ centralizer (V : Set G) := hFY.trans inf_le_right
  have hS2 := isPGroup_sup_of_le_centralizer (isPGroup_of_isKleinFour hF) hV2 hFV
  have hSQ : F ⊔ V ≤ coreActionKernel K'' :=
    sup_le (hFK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
      (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
  obtain ⟨t, htY, ht2, htQ⟩ := exists_orderOf_eq_two_not_mem_coreActionKernel hq hG hK''.1 hK''.2
    inf_le_left (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ)
  have htK'' : t ∈ K'' := htY.1
  have htF : t ∉ F := fun h => htQ (le_coreActionKernel_of_ne hK'' hK hK''K (hFK h))
  have htS : t ∈ centralizer ((F ⊔ V : Subgroup G) : Set G) := htY.2
  have htcF : t ∈ centralizer (F : Set G) :=
    centralizer_le (by exact_mod_cast le_sup_left) htS
  have htV : t ∈ centralizer (V : Set G) := centralizer_le (by exact_mod_cast le_sup_right) htS
  obtain ⟨hAe, hA8⟩ := isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hF) ht2 htF htcF
  have hAQ : F ⊔ zpowers t ≤ coreActionKernel K' :=
    sup_le (hFK.trans (le_coreActionKernel_of_ne hK' hK hne.symm))
      (zpowers_le.mpr (mem_coreActionKernel_of_ne hK'' hK' hK''K' htK''))
  have hAV : F ⊔ zpowers t ≤ centralizer (V : Set G) := sup_le hFV (zpowers_le.mpr htV)
  have hAN : F ⊔ zpowers t ≤ N := sup_le (hFK.trans hK.1.1) (zpowers_le.mpr (hK''.1.1 htK''))
  exact ⟨V, F ⊔ zpowers t, ⟨hK, hK', hne, hV, hVK', hAQ, hAV, hAe,
    by rw [hA8, hF.card_four], hAN, F, hF, le_sup_left, hFK⟩, hfV, mem_sup_left heF⟩

@[expose] def SigPairExistsTwoFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ e ∈ K, orderOf e = 2 → ∀ f ∈ K', orderOf f = 2 → f * e = e * f →
      ∃ V B : Subgroup G, (SigPair N K K' V B ∧ f ∈ V ∧ e ∈ B) ∨
        (SigPair N K' K V B ∧ e ∈ V ∧ f ∈ B)

theorem sigPairExistsFor_of_two (hq : QuasisimpleTwoPartInput) (h : SigPairExistsTwoFor) :
    SigPairExistsFor := by
  classical
  intro G _ _ hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe
  by_cases h2 : (kStarComponents N).ncard = 2
  · exact h G hG N hN h2 K hK K' hK' hne e heK he2 f hfK' hf2 hfe
  obtain ⟨K'', hK'', hK''K, hK''K'⟩ : ∃ K'' ∈ kStarComponents N, K'' ≠ K ∧ K'' ≠ K' := by
    by_contra hc
    push Not at hc
    have hsub : kStarComponents N ⊆ {K, K'} := fun J hJ => by
      by_cases hJK : J = K
      · exact Or.inl hJK
      · exact Or.inr (hc J hJ hJK)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hne] at hle
    have hge : 2 ≤ (kStarComponents N).ncard := by
      rw [← Set.ncard_pair hne]
      exact Set.ncard_le_ncard (Set.insert_subset hK (Set.singleton_subset_iff.mpr hK'))
        (Set.toFinite _)
    omega
  obtain ⟨V, B, hP⟩ := exists_sigPair_of_third hq hG hK hK' hne hK'' hK''K hK''K' heK he2 hfK' hf2
    hfe
  exact ⟨V, B, Or.inl hP⟩

theorem lemma315bInputFor_simple_of_rest (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39For) (hrest : GoodInvolutionsRestFor) (hsingle : SingleComponentExcludedFor)
    (hpair : SigPairExistsTwoFor) : Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_good hq hR1 hF h39 (goodInvolutionsFor_of_rest hq hR1 hrest) hsingle
    (sigPairExistsFor_of_two hq hpair)

end CFSG.ComponentClassification.Sol76.Sig
