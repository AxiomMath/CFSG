module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigDich

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem mem_solomonKStar_of_le_of_mem_kStarComponents {X B : Subgroup G}
    (hB : IsTwoComponentIn B X) {s : G} (hs2 : orderOf s = 2) (hsB : s ∈ coreActionKernel B)
    {J : Subgroup G} (hJ : J ∈ kStarComponents (centralizer ({s} : Set G))) (hJB : J ≤ B) :
    B ∈ solomonKStar G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({s} : Set G) with hC
  have hs2' : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
  have hcov := inf_centralizer_sup_oddCoreIn_eq hs2' (zpowers_le.mpr hsB)
  rw [centralizer_zpowers_eq] at hcov
  have hBq : IsQuasisimple (↥B ⧸ pPrimeCore 2 ↥B) :=
    isQuasisimple_quotient_of_isPComponent hB.1 hB.2
  obtain ⟨hJ2, hJL, hJsup, ⟨eJ⟩⟩ := cover_facts hBq inf_le_left hcov
  have hMY : IsTwoComponentIn J (B ⊓ C) :=
    isTwoComponentIn_of_le hJ.1 (le_inf hJB hJ.1.1) inf_le_right
  have hMJ : J = oddResidualIn (B ⊓ C) := by
    have hMle : J ≤ oddResidualIn (B ⊓ C) := hJL ▸ le_twoLayerIn_of_isTwoComponentIn hMY
    exact eq_of_le_of_le_isTwoComponentIn hMY hJ2 le_rfl hMle
      (UnbalancedCorr.commutator_eq_of_isPComponent hMY.1 hMY.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar hJ.2)
  rw [← hMJ] at hJsup eJ
  have hYdef : twoLayerIn (B ⊓ C) = J := hJL.trans hMJ.symm
  have hMn : B ⊓ C ≤ normalizer (J : Set G) := hYdef ▸ le_normalizer_twoLayerIn (B ⊓ C)
  have hOCM : oddCoreIn C ≤ normalizer (J : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hJ.1.1 hJ.1.2
  have hres : oddResidualIn (oddCoreIn C ⊔ (B ⊓ C)) = J := by
    apply le_antisymm
    · set W := oddCoreIn C ⊔ (oddCoreIn B ⊓ C) with hW
      have hWM : W ≤ normalizer (J : Set G) :=
        sup_le hOCM ((inf_le_inf_right _ (map_subtype_le _)).trans hMn)
      have hWodd : Odd (Nat.card W) := odd_card_sup_of_le_normalizer
        (inf_le_right.trans (le_normalizer_oddCoreIn C))
        (Nat.coprime_two_left.mp (coprime_card_oddCoreIn C))
        (Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
          (Subgroup.card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn B)))
      have hYle : B ⊓ C ≤ J ⊔ W := by
        intro y hy
        have hyB : y ∈ oddCoreIn B ⊔ J := by rw [sup_comm, hJsup]; exact hy.1
        obtain ⟨o, ho, m, hm, rfl⟩ := exists_mul_of_mem_sup_normalizer
          (hJB.trans (le_normalizer_oddCoreIn B)) hyB
        have hmC : m ∈ C := (hMY.1 hm).2
        have hoC : o ∈ C := by
          have e : o = o * m * m⁻¹ := by group
          rw [e]
          exact mul_mem hy.2 (inv_mem hmC)
        exact mul_mem (mem_sup_right (mem_sup_right ⟨ho, hoC⟩)) (mem_sup_left hm)
      have hle : oddCoreIn C ⊔ (B ⊓ C) ≤ J ⊔ W := sup_le (le_sup_left.trans le_sup_right) hYle
      rw [oddResidualIn, closure_le]
      rintro g ⟨hg, k, hk⟩
      exact mem_of_mem_sup_of_coprime_index hWM (Nat.Coprime.coprime_dvd_right
        (Subgroup.index_dvd_card _) (Nat.coprime_two_left.mpr hWodd)) (hle hg) hk
    · calc J = oddResidualIn (B ⊓ C) := hMJ
        _ ≤ oddResidualIn (oddCoreIn C ⊔ (B ⊓ C)) :=
          closure_mono fun g hg => ⟨mem_sup_right hg.1, hg.2⟩
  have hCU : centralizer ((zpowers s : Subgroup G) : Set G) = C := centralizer_zpowers_eq s
  have hmemB : IsSolomonMember B := by
    refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hB.1 hB.2, zpowers s,
      zpowers_ne_bot_of_orderOf_eq_two hs2, hs2', zpowers_le.mpr hsB, ?_⟩
    rw [hCU, hres]
    exact hJ.1
  have hmemM : IsSolomonMember J := hJ.2.1.1
  have hlt : SolomonLt B J := by
    refine ⟨hmemB, hmemM, zpowers s, hs2', zpowers_le.mpr hsB, ?_⟩
    rw [hCU, hYdef]
    have hcl : conjClosure J (twoLayerIn C) = J :=
      le_antisymm (Sol78.conjClosure_le le_rfl (twoLayerIn_le_normalizer hJ.1.1 hJ.1.2))
        (le_conjClosure J _)
    rw [hcl]
    exact isTwoComponentIn_of_le hJ.1 le_rfl hJ.1.1
  exact mem_solomonKStar_of_solomonEquiv hJ.2
    ⟨hmemM, Relation.ReflTransGen.single ⟨⟨Sol78.fusionZStarQuotOfCore eJ⟩, Or.inr hlt⟩⟩

variable {H : Subgroup G}

theorem exists_cover_eq_of_mem_kStarComponents (hq : QuasisimpleTwoPartInput)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N)
    (hcov : ∀ K ∈ kStarComponents N, ∃ M ∈ kStarComponents H, K ≤ M ∧ K ⊔ oddCoreIn M = M)
    {M : Subgroup G} (hM : M ∈ kStarComponents H) :
    ∃ K ∈ kStarComponents N, K ≤ M ∧ K ⊔ oddCoreIn M = M := by
  classical
  choose! f hf using hcov
  have hinj : Set.InjOn f (kStarComponents N) := fun K hK K' hK' heq => by
    obtain ⟨-, hKf, -⟩ := hf K hK
    obtain ⟨-, hK'f, hsup'⟩ := hf K' hK'
    rw [← heq] at hK'f hsup'
    exact eq_of_le_sup_oddCoreIn hK hK' hKf hK'f (hKf.trans hsup'.ge)
  have hsub : f '' kStarComponents N ⊆ kStarComponents H := by
    rintro _ ⟨K, hK, rfl⟩
    exact (hf K hK).1
  have hcard : (f '' kStarComponents N).ncard = (kStarComponents H).ncard := by
    refine le_antisymm (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
    rw [hinj.ncard_image]
    exact ncard_kStarComponents_le_of_simple hq hG hN H
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard.ge (Set.toFinite _)
  rw [← heq] at hM
  obtain ⟨K, hK, rfl⟩ := hM
  exact ⟨K, hK, (hf K hK).2⟩

theorem exists_le_of_mem_kStarComponents_centralizer (hN : IsSolomonChoice N)
    (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    (hcov : ∀ K ∈ kStarComponents N, ∃ M ∈ kStarComponents H, K ≤ M ∧ K ⊔ oddCoreIn M = M)
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {s : G} (hsK : s ∈ K) (hs2 : orderOf s = 2)
    {J : Subgroup G} (hJ : J ∈ kStarComponents (centralizer ({s} : Set G))) :
    ∃ M ∈ kStarComponents H, J ≤ M := by
  have hsH : s ∈ H := hKH K hK hsK
  have hLs : twoLayerIn (centralizer ({s} : Set G)) ≤ twoLayerIn H :=
    twoLayerIn_centralizer_le hsH (k := 1) (by rw [pow_one]; exact hs2) (hLH K hK s hsK hs2)
  have hJH : J ≤ H := (le_twoLayerIn_of_isTwoComponentIn hJ.1).trans (hLs.trans (map_subtype_le _))
  have hJHC : IsTwoComponentIn J (H ⊓ centralizer ({s} : Set G)) :=
    isTwoComponentIn_of_le hJ.1 (le_inf hJH hJ.1.1) inf_le_right
  obtain ⟨B, hBH, hBpc, hJB, -⟩ := foote_lemma_2_1_iv_subgroup hsH hs2 hJHC.1 hJHC.2
  have hLHB : twoLayerIn H ≤ normalizer (B : Set G) := twoLayerIn_le_normalizer hBH hBpc
  have hsL : s ∈ twoLayerIn H := le_twoLayerIn_of_le hN hKH hLH hK hsK
  have htB : conjugate B s = B := mem_normalizer_iff_map_conj_eq.mp (inv_mem (hLHB hsL))
  rw [htB, sup_idem] at hJB
  obtain ⟨M, hM, hKM, -⟩ := hcov K hK
  by_cases hBM : B = M
  · exact ⟨B, hBM ▸ hM, hJB⟩
  · have hsB : s ∈ coreActionKernel B :=
      GSThmB.B5a.le_coreActionKernel_of_ne hBH hM.1.1 hBpc hM.1.2 hBM (hKM hsK)
    exact ⟨B, ⟨⟨hBH, hBpc⟩, mem_solomonKStar_of_le_of_mem_kStarComponents ⟨hBH, hBpc⟩ hs2 hsB hJ
      hJB⟩, hJB⟩

theorem eq_of_le_of_mem_kStarComponents_centralizer (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    (hcov : ∀ K ∈ kStarComponents N, ∃ M ∈ kStarComponents H, K ≤ M ∧ K ⊔ oddCoreIn M = M)
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {s : G} (hsK : s ∈ K) (hs2 : orderOf s = 2)
    {M J J' : Subgroup G} (hM : M ∈ kStarComponents H)
    (hJ : J ∈ kStarComponents (centralizer ({s} : Set G)))
    (hJ' : J' ∈ kStarComponents (centralizer ({s} : Set G))) (hJM : J ≤ M) (hJ'M : J' ≤ M) :
    J = J' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({s} : Set G) with hC
  obtain ⟨MK, hMK, hKMK, hKsup⟩ := hcov K hK
  by_cases hMM : M = MK
  swap
  ·
    have hsM : s ∈ coreActionKernel M :=
      GSThmB.B5a.le_coreActionKernel_of_ne hM.1.1 hMK.1.1 hM.1.2 hMK.1.2 hMM (hKMK hsK)
    have hs2' : IsPGroup 2 (zpowers s) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
    have hcovM := inf_centralizer_sup_oddCoreIn_eq hs2' (zpowers_le.mpr hsM)
    rw [centralizer_zpowers_eq] at hcovM
    obtain ⟨hR2, hRL, -, -⟩ := cover_facts (isQuasisimple_quotient_of_isPComponent hM.1.1 hM.1.2)
      inf_le_left hcovM
    have hJY : IsTwoComponentIn J (M ⊓ C) := isTwoComponentIn_of_le hJ.1 (le_inf hJM hJ.1.1)
      inf_le_right
    have hJ'Y : IsTwoComponentIn J' (M ⊓ C) := isTwoComponentIn_of_le hJ'.1
      (le_inf hJ'M hJ'.1.1) inf_le_right
    have h1 : J = oddResidualIn (M ⊓ C) := eq_of_le_of_le_isTwoComponentIn hJY hR2 le_rfl
      (hRL ▸ le_twoLayerIn_of_isTwoComponentIn hJY)
      (UnbalancedCorr.commutator_eq_of_isPComponent hJY.1 hJY.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar hJ.2)
    have h2 : J' = oddResidualIn (M ⊓ C) := eq_of_le_of_le_isTwoComponentIn hJ'Y hR2 le_rfl
      (hRL ▸ le_twoLayerIn_of_isTwoComponentIn hJ'Y)
      (UnbalancedCorr.commutator_eq_of_isPComponent hJ'Y.1 hJ'Y.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar hJ'.2)
    rw [h1, h2]
  subst hMM
  by_contra hne
  have hpump : ∀ K' ∈ kStarComponents N \ {K}, ∃ P ∈ kStarComponents C,
      ∃ M' ∈ kStarComponents H, K' ≤ M' ∧ K' ⊔ oddCoreIn M' = M' ∧ P ≤ M' := by
    intro K' hK'
    obtain ⟨hK'N, hK'K⟩ := hK'
    have hne' : K' ≠ K := hK'K
    obtain ⟨P, hP, B', hB', hPB', hK'B', -⟩ := exists_pump_le hq hR1 hG hN hKH hLH hK'N hK hne'
      hsK hs2
    obtain ⟨M', hM', hK'M', hK'sup⟩ := hcov K' hK'N
    have hB'M' : B' = M' := eq_of_le_of_le_isTwoComponentIn hB' hM'.1 hK'B' hK'M'
      (UnbalancedCorr.commutator_eq_of_isPComponent hK'N.1.1 hK'N.1.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar hK'N.2)
    exact ⟨P, hP.1, M', hM', hK'M', hK'sup, hB'M' ▸ hPB'⟩
  choose! P hP M' hM' hK'M' hK'sup hPM' using hpump
  have hPinj : Set.InjOn P (kStarComponents N \ {K}) := by
    intro K₁ hK₁ K₂ hK₂ heq
    have hMeq : M' K₁ = M' K₂ := eq_of_le_of_le_isTwoComponentIn (hM' K₁ hK₁).1 (hM' K₂ hK₂).1
      (hPM' K₁ hK₁) (heq ▸ hPM' K₂ hK₂)
      (UnbalancedCorr.commutator_eq_of_isPComponent (hP K₁ hK₁).1.1 (hP K₁ hK₁).1.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar (hP K₁ hK₁).2)
    have h2 := hK'sup K₂ hK₂
    rw [← hMeq] at h2
    exact eq_of_le_sup_oddCoreIn hK₁.1 hK₂.1 (hK'M' K₁ hK₁) (hMeq ▸ hK'M' K₂ hK₂)
      ((hK'M' K₁ hK₁).trans h2.ge)
  have hPne : ∀ K' ∈ kStarComponents N \ {K}, ∀ Y ∈ kStarComponents C, Y ≤ M → P K' ≠ Y := by
    intro K' hK' Y hY hYM hPY
    have hMeq : M' K' = M := eq_of_le_of_le_isTwoComponentIn (hM' K' hK').1 hMK.1
      (hPM' K' hK') (hPY ▸ hYM)
      (UnbalancedCorr.commutator_eq_of_isPComponent (hP K' hK').1.1 (hP K' hK').1.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar (hP K' hK').2)
    have h2 := hK'sup K' hK'
    rw [hMeq] at h2
    exact hK'.2 (eq_of_le_sup_oddCoreIn hK'.1 hK (hMeq ▸ hK'M' K' hK') hKMK
      ((hMeq ▸ hK'M' K' hK').trans hKsup.ge))
  have hsub : P '' (kStarComponents N \ {K}) ∪ {J, J'} ⊆ kStarComponents C := by
    rintro Y (⟨K', hK', rfl⟩ | hY)
    · exact hP K' hK'
    · rcases hY with rfl | rfl
      · exact hJ
      · exact hJ'
  have hdisj : Disjoint (P '' (kStarComponents N \ {K})) {J, J'} := by
    rw [Set.disjoint_left]
    rintro _ ⟨K', hK', rfl⟩ hY
    rcases hY with h | h
    · exact hPne K' hK' J hJ hJM h
    · exact hPne K' hK' J' hJ' hJ'M h
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hPinj.ncard_image,
    Set.ncard_pair hne, Set.ncard_sdiff_singleton_of_mem hK] at hcard
  have hle := ncard_kStarComponents_le_of_simple hq hG hN C
  have hpos : 1 ≤ (kStarComponents N).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨K, hK⟩
  omega

end CFSG.ComponentClassification.Sol76.Sig
