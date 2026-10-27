module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL312

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

@[expose] def GoodInvolutionsFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

theorem wGroup_eq_bot_of_good (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39For) (hgood : GoodInvolutionsFor) (hsingle : SingleComponentExcludedFor)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N) {V B : Subgroup G}
    (hP : SigPair N K K' V B) : wGroup B V = ⊥ := by
  by_contra hW
  set H := normalizer (wGroup B V : Set G) with hH
  have hKH := h39 G hG N hN K K' V B hP hW
  have hfacts : ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
      twoLayerIn (centralizer ({x} : Set G)) ≤ H ∧ oddCoreIn (centralizer ({x} : Set G)) ≤ H ∧
        oddCoreIn H ⊓ centralizer ({x} : Set G) ≤ oddCoreIn (centralizer ({x} : Set G)) := by
    intro K'' hK'' x hx hx2
    obtain ⟨g, hg, hgx⟩ := hgood G hG N hN K K' V B hP hW hKH K'' hK'' x hx hx2
    exact good_facts_of_conj hg (good_facts hq hR1 hG hN hKH hgx)
  have hLH : ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
      twoLayerIn (centralizer ({x} : Set G)) ≤ H := fun K'' hK'' x hx hx2 =>
    (hfacts K'' hK'' x hx hx2).1
  rcases cover_or_single hq hR1 hG hN hKH hLH with hcov | ⟨M, hM, hMK⟩
  · obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, -, E, hE, hEB, hEK⟩ := hP
    have hOW := oddCoreIn_normalizer_wGroup_eq hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE
      hEB hEK (hKH K hK) (hKH K' hK')
    have hHO : normalizer (oddCoreIn H : Set G) ≤ H := by rw [hOW]
    exact false_of_cover hq hF hG hN hcov fun K'' hK'' s hs hs2 =>
      centralizer_le_of_cover hq hR1 hG hN hKH hcov hfacts hHO hK'' hs hs2
  · exact hsingle G hG N hN K K' V B hP hW hKH hLH M hM hMK

theorem lemma315bInputFor_simple_of_good (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39For) (hgood : GoodInvolutionsFor) (hsingle : SingleComponentExcludedFor)
    (hpair : SigPairExistsFor) : Lemma315bInputFor simpleAmbient := by
  refine lemma315bInputFor_of_separated (lemma32FullFor_simple_of_twoPart hq hR1) ?_
  intro G _ _ hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he2; norm_num at he2
  have hf1 : f ≠ 1 := fun h => by rw [h, orderOf_one] at hf2; norm_num at hf2
  obtain ⟨V, B, hVB | hVB⟩ := hpair G hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe
  · obtain ⟨hP, hfV, heB⟩ := hVB
    have hW := wGroup_eq_bot_of_good hq hR1 hF h39 hgood hsingle hG hN hP
    exact eq_bot_iff.mpr ((oddCoreIn_inf_le_wGroup hP.2.2.2.1 hP.2.2.2.2.2.2.1 heB he1
      hfV).trans hW.le)
  · obtain ⟨hP, heV, hfB⟩ := hVB
    have hW := wGroup_eq_bot_of_good hq hR1 hF h39 hgood hsingle hG hN hP
    rw [inf_comm]
    exact eq_bot_iff.mpr ((oddCoreIn_inf_le_wGroup hP.2.2.2.1 hP.2.2.2.2.2.2.1 hfB hf1
      heV).trans hW.le)

theorem isGoodFor_of_mem_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {V B : Subgroup G} (hP : SigPair N K K' V B) {E : Subgroup G}
    (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K) {K'' : Subgroup G}
    (hK'' : K'' ∈ kStarComponents N) (hK''K' : K'' ≠ K') {t : G} (htK'' : t ∈ K'')
    (ht2 : orderOf t = 2) (hEt : E ≤ centralizer ({t} : Set G))
    (hVt : V ≤ centralizer ({t} : Set G)) : IsGoodFor N (wGroup B V) t := by
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, -⟩ := hP
  by_cases htE : t ∈ E
  · exact ⟨ht1, K, K', V, B, ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩,
      rfl, Or.inl (hEB htE)⟩
  have hsc : t ∈ centralizer (E : Set G) := mem_centralizer_iff.mpr fun e he =>
    mem_centralizer_singleton_iff.mp (hEt he)
  obtain ⟨hAe, hA8⟩ :=
    isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hE) ht2 htE hsc
  have htQ : t ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK'' hK' hK''K' htK''
  have hAQ : E ⊔ zpowers t ≤ coreActionKernel K' := sup_le (hEB.trans hBQ) (zpowers_le.mpr htQ)
  have htV : t ∈ centralizer (V : Set G) := mem_centralizer_iff.mpr fun w hw =>
    mem_centralizer_singleton_iff.mp (hVt hw)
  have hAV : E ⊔ zpowers t ≤ centralizer (V : Set G) :=
    sup_le (hEB.trans hBV) (zpowers_le.mpr htV)
  have hAN : E ⊔ zpowers t ≤ N := sup_le (hEB.trans hBN) (zpowers_le.mpr (hK''.1.1 htK''))
  have hW : wGroup (E ⊔ zpowers t) V = wGroup B V :=
    (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hAe hE le_sup_left hEK hE
      le_sup_left).symm.trans
      (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB)
  exact ⟨ht1, K, K', V, E ⊔ zpowers t, ⟨hK, hK', hne, hV, hVK', hAQ, hAV, hAe,
    by rw [hA8, hE.card_four], hAN, E, hE, le_sup_left, hEK⟩, hW,
    Or.inl (mem_sup_right (mem_zpowers t))⟩

theorem isGoodFor_of_mem_right (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {V B : Subgroup G} (hP : SigPair N K K' V B) {E : Subgroup G}
    (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (hconn : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected)
    {t : G} (htY : t ∈ K' ⊓ centralizer (B : Set G)) (ht2 : orderOf t = 2) :
    IsGoodFor N (wGroup B V) t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, -⟩ := hP
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  obtain ⟨htK', htB⟩ := mem_inf.mp htY
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  have hsupB := inf_centralizer_sup_oddCoreIn_eq hB2 hBQ
  have hBt : B ≤ centralizer ({t} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp htB) b hb)
  have hEt : E ≤ centralizer ({t} : Set G) := hEB.trans hBt
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hv2 := orderOf_eq_two_of_isKleinFour hV hvV hv1
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hvY : v ∈ K' ⊓ centralizer (E : Set G) := ⟨hVK' hvV, mem_centralizer_iff.mpr fun e he =>
    ((mem_centralizer_iff.mp (hEV he)) v hvV).symm⟩
  have htY' : t ∈ K' ⊓ centralizer (E : Set G) := ⟨htK', mem_centralizer_iff.mpr fun e he =>
    mem_centralizer_singleton_iff.mp (hEt he)⟩
  have hWv : wGroup E (zpowers v) = wGroup B V := by
    rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV hVK' hE hEK hEV hvV hv1]
    exact wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hWt : wGroup E (zpowers t) = wGroup B V := by
    rw [← hWv]
    exact (wGroup_zpowers_eq_of_reachable h32 hG hN hK hK' hne hE hEK
      (hconn ⟨⟨v, hvY⟩, by rw [Subgroup.orderOf_mk]; exact hv2⟩
        ⟨⟨t, htY'⟩, by rw [Subgroup.orderOf_mk]; exact ht2⟩)).symm
  have hrank : 2 ≤ CFSG.Open.pRank 2 (K' ⊓ centralizer (B : Set G)) :=
    (two_le_pRank_of_mem_solomonKStar hK'.2).trans (pRank_le_of_sup_oddCoreIn inf_le_left hsupB)
  obtain ⟨Vt, hVtY, hVt, htVt⟩ := exists_isKleinFour_mem hrank htY ht2
  have hVtK' : Vt ≤ K' := hVtY.trans inf_le_left
  have hBVt : B ≤ centralizer (Vt : Set G) := fun b hb => mem_centralizer_iff.mpr fun w hw =>
    ((mem_centralizer_iff.mp (hVtY hw).2) b hb).symm
  have hWVt : wGroup B Vt = wGroup B V := by
    rw [← wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hVt hVtK' hBQ hBVt hB hE hEB hEK hE hEB,
      wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hVt hVtK' hE hEK (hEB.trans hBVt) htVt ht1]
    exact hWt
  exact ⟨ht1, K, K', Vt, B, ⟨hK, hK', hne, hVt, hVtK', hBQ, hBVt, hB, hB8, hBN, E, hE, hEB, hEK⟩,
    hWVt, Or.inr htVt⟩

theorem exists_isGoodFor_of_mem_left (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {V B : Subgroup G} (hP : SigPair N K K' V B) {E : Subgroup G}
    (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F)
    {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N) (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K')
    {t : G} (hs : t ∈ K ⊓ centralizer (V : Set G)) (ht2 : orderOf t = 2) :
    ∃ g ∈ K'', IsGoodFor N (wGroup B V) (g⁻¹ * t * g) := by
  classical
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, -⟩ := hP'
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hrank : 2 ≤ CFSG.Open.pRank 2 (K ⊓ centralizer (V : Set G)) :=
    (two_le_pRank_of_mem_solomonKStar hK.2).trans
      (pRank_le_of_sup_oddCoreIn inf_le_left (inf_centralizer_sup_oddCoreIn_eq hV2 hVQ))
  obtain ⟨F, hFX, hF, htF⟩ := exists_isKleinFour_mem hrank hs ht2
  have hFK : F ≤ K := hFX.trans inf_le_left
  have hFV : F ≤ centralizer (V : Set G) := hFX.trans inf_le_right
  have hWF : wGroup F V = wGroup B V :=
    (wGroup_eq_of_reflTransGen h32 hG hN hK hK' hne hV hVK' (hconn F hF hFX)).trans
      (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB)
  have hS2 := isPGroup_sup_of_le_centralizer (isPGroup_of_isKleinFour hF) hV2 hFV
  have hSQ : F ⊔ V ≤ coreActionKernel K'' :=
    sup_le (hFK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
      (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
  have hrank'' : 2 ≤ CFSG.Open.pRank 2 (K'' ⊓ centralizer ((F ⊔ V : Subgroup G) : Set G)) :=
    (two_le_pRank_of_mem_solomonKStar hK''.2).trans
      (pRank_le_of_sup_oddCoreIn inf_le_left (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ))
  obtain ⟨u, hu, hu2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hrank'')
  obtain ⟨T, hTY, hT, -⟩ := exists_isKleinFour_mem hrank'' hu hu2
  by_cases hTF : T ≤ F
  ·
    have hTF' : T = F := eq_of_le_of_card_ge hTF (le_of_eq (by rw [hT.card_four, hF.card_four]))
    have htT : t ∈ T := by rw [hTF']; exact htF
    have htK'' : t ∈ K'' := (hTY.trans inf_le_left) htT
    have hE2 := isPGroup_of_isKleinFour hE
    have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
    have hS2' := isPGroup_sup_of_le_centralizer hE2 hV2 hEV
    have hSQ' : E ⊔ V ≤ coreActionKernel K'' :=
      sup_le (hEK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
        (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
    obtain ⟨m, hm, hmS⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq hS2' hSQ') htK'' ht2
    refine ⟨m, hm, ?_⟩
    have hm2 : orderOf (m⁻¹ * t * m) = 2 := by rw [orderOf_inv_mul_mul, ht2]
    obtain ⟨hmK'', hmC⟩ := mem_inf.mp hmS
    exact isGoodFor_of_mem_third hq hR1 hG hN hP hE hEB hEK hK'' hK''K' hmK'' hm2
      (fun e he => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hmC) e (le_sup_left (b := V) he)))
      (fun w hw => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hmC) w (le_sup_right (a := E) hw)))
  refine ⟨1, one_mem _, ?_⟩
  rw [inv_one, one_mul, mul_one]
  obtain ⟨t', ht'T, ht'F⟩ : ∃ t' ∈ T, t' ∉ F := by
    by_contra h
    push Not at h
    exact hTF fun x hx => h x hx
  have ht'1 : t' ≠ 1 := fun h => ht'F (h ▸ F.one_mem)
  have ht'2 : orderOf t' = 2 := orderOf_eq_two_of_isKleinFour hT ht'T ht'1
  have ht'K'' : t' ∈ K'' := (hTY.trans inf_le_left) ht'T
  have ht'S : t' ∈ centralizer ((F ⊔ V : Subgroup G) : Set G) := (hTY.trans inf_le_right) ht'T
  have ht'F' : t' ∈ centralizer (F : Set G) := centralizer_le (by exact_mod_cast le_sup_left) ht'S
  have ht'V : t' ∈ centralizer (V : Set G) := centralizer_le (by exact_mod_cast le_sup_right) ht'S
  obtain ⟨hAe, hA8⟩ :=
    isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hF) ht'2 ht'F ht'F'
  have hAQ : F ⊔ zpowers t' ≤ coreActionKernel K' :=
    sup_le (hFK.trans (le_coreActionKernel_of_ne hK' hK hne.symm))
      (zpowers_le.mpr (mem_coreActionKernel_of_ne hK'' hK' hK''K' ht'K''))
  have hAV : F ⊔ zpowers t' ≤ centralizer (V : Set G) := sup_le hFV (zpowers_le.mpr ht'V)
  have hAN : F ⊔ zpowers t' ≤ N := sup_le (hFK.trans hK.1.1) (zpowers_le.mpr (hK''.1.1 ht'K''))
  have hW : wGroup (F ⊔ zpowers t') V = wGroup B V :=
    (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hAe hF le_sup_left hFK hF
      le_sup_left).symm.trans hWF
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  exact ⟨ht1, K, K', V, F ⊔ zpowers t', ⟨hK, hK', hne, hV, hVK', hAQ, hAV, hAe,
    by rw [hA8, hF.card_four], hAN, F, hF, le_sup_left, hFK⟩, hW, Or.inl (mem_sup_left htF)⟩

theorem exists_isGoodFor_of_connected (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {V B : Subgroup G} (hP : SigPair N K K' V B) {E : Subgroup G}
    (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (hconn' : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F)
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ kStarComponents N) (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K')
    (hKH : ∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G))
    {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N) {x : G} (hx : x ∈ K'')
    (hx2 : orderOf x = 2) :
    ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g) := by
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, -⟩ := hP'
  have hV2 := isPGroup_of_isKleinFour hV
  by_cases h1 : K'' = K
  · subst h1
    have hVQ : V ≤ coreActionKernel K'' := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
    obtain ⟨k, hk, hkV⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq hV2 hVQ) hx hx2
    have hk2 : orderOf (k⁻¹ * x * k) = 2 := by rw [orderOf_inv_mul_mul, hx2]
    obtain ⟨g, hg, hgood⟩ := exists_isGoodFor_of_mem_left hq hR1 hG hN hP hE hEB hEK hconn hK₃ hK₃K
      hK₃K' hkV hk2
    refine ⟨k * g, mul_mem (hKH K'' hK hk) (hKH K₃ hK₃ hg), ?_⟩
    rwa [show (k * g)⁻¹ * x * (k * g) = g⁻¹ * (k⁻¹ * x * k) * g by group]
  by_cases h2 : K'' = K'
  · subst h2
    have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
    obtain ⟨k, hk, hkB⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq hB2 hBQ) hx hx2
    have hk2 : orderOf (k⁻¹ * x * k) = 2 := by rw [orderOf_inv_mul_mul, hx2]
    exact ⟨k, hKH K'' hK' hk, isGoodFor_of_mem_right hq hR1 hG hN hP hE hEB hEK hconn' hkB hk2⟩
  · have hE2 := isPGroup_of_isKleinFour hE
    have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
    have hS2 := isPGroup_sup_of_le_centralizer hE2 hV2 hEV
    have hSQ : E ⊔ V ≤ coreActionKernel K'' :=
      sup_le (hEK.trans (le_coreActionKernel_of_ne hK'' hK h1))
        (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' h2))
    obtain ⟨m, hm, hmS⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ) hx hx2
    have hm2 : orderOf (m⁻¹ * x * m) = 2 := by rw [orderOf_inv_mul_mul, hx2]
    obtain ⟨hmK'', hmC⟩ := mem_inf.mp hmS
    exact ⟨m, hKH K'' hK'' hm, isGoodFor_of_mem_third hq hR1 hG hN hP hE hEB hEK hK'' h2 hmK'' hm2
      (fun e he => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hmC) e (le_sup_left (b := V) he)))
      (fun w hw => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hmC) w (le_sup_right (a := E) hw)))⟩

@[expose] def GoodInvolutionsRestFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ¬ (∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧
          (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected ∧
          (∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) ∧
          ∃ K₃ ∈ kStarComponents N, K₃ ≠ K ∧ K₃ ≠ K') →
      ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

theorem goodInvolutionsFor_of_rest (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h : GoodInvolutionsRestFor) :
    GoodInvolutionsFor := by
  intro G _ _ hG N hN K K' V B hP hW hKH K'' hK'' x hx hx2
  by_cases hgood : ∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧
      (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected ∧
      (∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
        Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) ∧
      ∃ K₃ ∈ kStarComponents N, K₃ ≠ K ∧ K₃ ≠ K'
  · obtain ⟨E, hE, hEB, hEK, hconn', hconn, K₃, hK₃, hK₃K, hK₃K'⟩ := hgood
    exact exists_isGoodFor_of_connected hq hR1 hG hN hP hE hEB hEK hconn' hconn hK₃ hK₃K hK₃K'
      hKH hK'' hx hx2
  · exact h G hG N hN K K' V B hP hW hKH hgood K'' hK'' x hx hx2

end CFSG.ComponentClassification.Sol76.Sig
