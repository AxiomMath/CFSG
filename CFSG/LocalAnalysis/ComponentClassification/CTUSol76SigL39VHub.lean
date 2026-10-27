module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39Hub
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigQJoin

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem theta_inf_le_oddCoreIn_of_bound (hK : K ∈ kStarComponents N) {V : Subgroup G}
    (hV : IsKleinFour V) (hVQ : V ≤ coreActionKernel K)
    (hbound : ∀ w ∈ V, w ≠ 1 →
      conjClosure (twoLayerIn (K ⊓ centralizer ({w} : Set G)))
          (twoLayerIn (centralizer ({w} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({w} : Set G))) ⊔
          twoLayerIn (K ⊓ centralizer ({w} : Set G)))
    {f : G} (hfK : f ∈ K) (hf2 : orderOf f = 2) (hfV : V ≤ centralizer ({f} : Set G))
    {u : G} (huV : u ∈ V) (hu1 : u ≠ 1) :
    theta V f ⊓ centralizer ({u} : Set G) ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  have hSp : IsPGroup 2 (zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
  have hlocal : ∀ w ∈ V, w ≠ 1 → ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({w} : Set G)) →
        zpowers f ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G)) := by
    intro w hw hw1 M hM
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hV hw hw1
    have hVw : V ≤ centralizer ({w} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hV x hx w hw)
    have hfw : f ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_singleton_iff.mp (hfV hw)).symm)
    exact component_dichotomy_of_pump_of_le hK (hVQ hw) hw2 (hbound w hw hw1)
      (S₁ := zpowers f) (S₂ := V) hSp
      (le_inf (zpowers_le.mpr hfK) (zpowers_le.mpr hfw)) hVQ hVw M hM
  exact theta_inf_le_oddCoreIn_of_component_dichotomy hV hf2 hfV hlocal huV hu1

theorem theta_le_theta_zpowers_of_bound (hK : K ∈ kStarComponents N) {V : Subgroup G}
    (hV : IsKleinFour V) (hVQ : V ≤ coreActionKernel K)
    (hbound : ∀ w ∈ V, w ≠ 1 →
      conjClosure (twoLayerIn (K ⊓ centralizer ({w} : Set G)))
          (twoLayerIn (centralizer ({w} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({w} : Set G))) ⊔
          twoLayerIn (K ⊓ centralizer ({w} : Set G)))
    {e : G} (heK : e ∈ K) (he2 : orderOf e = 2) (heV : V ≤ centralizer ({e} : Set G))
    {u : G} (huV : u ∈ V) (hu1 : u ≠ 1) :
    theta V e ≤ theta (zpowers u) e :=
  (theta_eq_theta_zpowers_of_fixed_bound hV heV huV hu1
    (theta_inf_le_oddCoreIn_of_bound hK hV hVQ hbound heK he2 heV huV hu1)).le

theorem wGroup_zpowers_eq_of_four (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {E F : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) (hF : IsKleinFour F)
    (hFK' : F ≤ K') {u u' : G} (hu2 : orderOf u = 2) (hu'2 : orderOf u' = 2)
    (huu' : u * u' = u' * u) (huQ : u ∈ coreActionKernel K) (hu'Q : u' ∈ coreActionKernel K)
    (hFu : F ≤ centralizer ({u} : Set G)) (hFu' : F ≤ centralizer ({u'} : Set G))
    (hEu : E ≤ centralizer ({u} : Set G)) (hEu' : E ≤ centralizer ({u'} : Set G)) :
    wGroup E (zpowers u) = wGroup E (zpowers u') := by
  classical
  by_cases hne' : u = u'
  · rw [hne']
  set V := closure ({u, u'} : Set G) with hVdef
  have hV : IsKleinFour V :=
    UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hu2 hu'2 huu' hne'
  have huV : u ∈ V := subset_closure (Set.mem_insert u _)
  have hu'V : u' ∈ V := subset_closure (Set.mem_insert_of_mem u rfl)
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; norm_num at hu2
  have hu'1 : u' ≠ 1 := fun h => by rw [h, orderOf_one] at hu'2; norm_num at hu'2
  have hV2 := isPGroup_of_isKleinFour hV
  have hVc := comm_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := by
    rw [hVdef, closure_le]
    rintro x (rfl | rfl)
    · exact huQ
    · exact hu'Q
  have hVF : V ≤ centralizer (F : Set G) := by
    rw [hVdef, closure_le]
    rintro x (rfl | rfl)
    · exact mem_centralizer_iff.mpr fun f hf => mem_centralizer_singleton_iff.mp (hFu hf)
    · exact mem_centralizer_iff.mpr fun f hf => mem_centralizer_singleton_iff.mp (hFu' hf)
  have hbound : ∀ w ∈ V, w ≠ 1 →
      conjClosure (twoLayerIn (K ⊓ centralizer ({w} : Set G)))
          (twoLayerIn (centralizer ({w} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({w} : Set G))) ⊔
          twoLayerIn (K ⊓ centralizer ({w} : Set G)) := fun w hw hw1 =>
    conjClosure_le_of_isKleinFour hq hR1 hG hN hK hK' hne (hVQ hw)
      (orderOf_eq_two_of_isKleinFour hV hw hw1) hF hFK' fun f hf =>
        mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hVF hw)) f hf)
  have hVe : ∀ e ∈ E, V ≤ centralizer ({e} : Set G) := fun e he => by
    rw [hVdef, closure_le]
    rintro x (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hEu he)).symm
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hEu' he)).symm
  have hθ : ∀ e ∈ E, e ≠ 1 → theta (zpowers u) e = theta (zpowers u') e := fun e he he1 => by
    have he2 := orderOf_eq_two_of_isKleinFour hE he he1
    have h1 : theta (zpowers u) e = theta V e :=
      le_antisymm (theta_mono (zpowers_le.mpr huV) hV2 hVc (hVe e he))
        (theta_le_theta_zpowers_of_bound hK hV hVQ hbound (hEK he) he2 (hVe e he) huV hu1)
    have h2 : theta (zpowers u') e = theta V e :=
      le_antisymm (theta_mono (zpowers_le.mpr hu'V) hV2 hVc (hVe e he))
        (theta_le_theta_zpowers_of_bound hK hV hVQ hbound (hEK he) he2 (hVe e he) hu'V hu'1)
    rw [h1, h2]
  refine le_antisymm (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  · rw [hθ e he he1]
    exact theta_le_wGroup he he1
  · rw [← hθ e he he1]
    exact theta_le_wGroup he he1

theorem le_normalizer_wGroup_of_vhub (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N) {z : G} (hz2 : orderOf z = 2)
    (hzQ : z ∈ coreActionKernel K) (hzQ' : z ∈ coreActionKernel K')
    (hzV : z ∈ centralizer (V : Set G)) (hzE : z ∈ centralizer (E : Set G)) :
    K' ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hEc := comm_of_isKleinFour hE
  have hEE : E ≤ centralizer (E : Set G) := le_centralizer_of_le_of_comm le_rfl hEc
  have hVc := comm_of_isKleinFour hV
  obtain ⟨v, hv, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hv2 := orderOf_eq_two_of_isKleinFour hV hv hv1
  have hWv : wGroup E V = wGroup E (zpowers v) :=
    wGroup_eq_wGroup_zpowers_of_mem hq hR1 hG hN hK hK' hne hV hVK' hE (hEB.trans hBQ) hEV hE hEK
      hEV hEE hv hv1
  have hVv : V ≤ centralizer ({v} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (hVc w hw v hv)
  have hVz : V ≤ centralizer ({z} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzV) w hw)
  have hvz : v * z = z * v := (mem_centralizer_iff.mp hzV) v hv
  have hEv : E ≤ centralizer ({v} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV he)) v hv).symm
  have hEz : E ≤ centralizer ({z} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzE) e he)
  have hWz : wGroup E (zpowers v) = wGroup E (zpowers z) :=
    wGroup_zpowers_eq_of_four hq hR1 hG hN hK hK' hne hE hEK hV hVK' hv2 hz2 hvz
      ((hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)) hv) hzQ hVv hVz hEv hEz
  have hW : wGroup E (zpowers z) = wGroup B V := by rw [← hWz, ← hWv, hWE]
  have hzz : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
  have hEzc : zpowers z ≤ centralizer (E : Set G) := zpowers_le.mpr hzE
  have hS2 : IsPGroup 2 (E ⊔ zpowers z : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_of_isKleinFour hE) hzz
      ((le_centralizer_iff.1 hEzc).trans (centralizer_le_normalizer _))
  have hSQ : E ⊔ zpowers z ≤ coreActionKernel K' :=
    sup_le (hEK.trans (le_coreActionKernel_of_ne hK' hK hne.symm)) (zpowers_le.mpr hzQ')
  rw [← inf_centralizer_sup_oddCoreIn_eq hS2 hSQ]
  refine sup_le ?_ ?_
  · intro g hg
    have hgE : g ∈ centralizer (E : Set G) :=
      centralizer_le (by exact_mod_cast (le_sup_left : E ≤ E ⊔ zpowers z)) hg.2
    have hgz : g ∈ centralizer ((zpowers z : Subgroup G) : Set G) :=
      centralizer_le (by exact_mod_cast (le_sup_right : zpowers z ≤ E ⊔ zpowers z)) hg.2
    have hEg : E.map (MulAut.conj g).toMonoidHom = E := map_conj_eq_of_mem_centralizer hgE
    have hzg : (zpowers z).map (MulAut.conj g).toMonoidHom = zpowers z :=
      map_conj_eq_of_mem_centralizer hgz
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [← hW, map_wGroup, hEg, hzg]
    exact mem_normalizer_iff_map_conj_eq.mpr key
  · exact (oddCoreIn_le_of_isTwoComponentIn hK'.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

theorem exists_vhub (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N) {z₀ : G}
    (hz₀ : z₀ ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N))
    (hz₀2 : orderOf z₀ = 2) {V E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hE : IsKleinFour E) (hEK : E ≤ K) (hEV : E ≤ centralizer (V : Set G)) :
    ∃ b : G, orderOf b = 2 ∧ b ∈ coreActionKernel K' ∧ b ∈ coreActionKernel K ∧
      b ∈ centralizer (V : Set G) ∧ b ∈ centralizer (E : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : z₀ ∈ kStarKernel N :=
    ⟨(sup_le (map_subtype_le _) (map_subtype_le _)) hz₀.1, hz₀.2⟩
  have heven : Even (Nat.card (kStarKernel N)) := by
    have hdvd := (kStarKernel N).orderOf_dvd_natCard hzK
    rw [hz₀2] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  set P := E ⊔ V with hP
  have hPsq : ∀ x ∈ P, x ^ 2 = 1 :=
    FooteLit.sq_eq_one_of_mem_sup (fun x hx => Sig.sq_eq_one_of_isKleinFour hE hx)
      (fun x hx => Sig.sq_eq_one_of_isKleinFour hV hx) fun x hx y hy =>
        ((mem_centralizer_iff.mp (hEV hx)) y hy).symm
  have hPN : P ≤ normalizer (kStarKernel N : Set G) :=
    (sup_le (hEK.trans (le_of_mem_kStarComponents hK))
      (hVK'.trans (le_of_mem_kStarComponents hK'))).trans (le_normalizer_kStarKernel N)
  obtain ⟨b, hbC, hb2, hbP⟩ := CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer
    (isPGroup_of_sq_eq_one hPsq) hPN heven
  exact ⟨b, hb2, kStarKernel_le_coreActionKernel hK' hbC, kStarKernel_le_coreActionKernel hK hbC,
    mem_centralizer_iff.mpr fun v hv => hbP v (mem_sup_right hv),
    mem_centralizer_iff.mpr fun x hx => hbP x (mem_sup_left hx)⟩

theorem not_mem_of_center_eq_bot (hZ : center (coreQuot K) = ⊥) {b : G} (hb2 : orderOf b = 2)
    (hbQ : b ∈ coreActionKernel K) : b ∉ K := by
  intro hbK
  have h1 := mk_mem_center_of_mem_coreActionKernel (u := ⟨b, hbK⟩) hbQ
  rw [hZ, mem_bot] at h1
  have hbO : b ∈ oddCoreIn K := mk_eq_one_iff.mp h1
  have hO : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hdvd := (oddCoreIn K).orderOf_dvd_natCard hbO
  rw [hb2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)

@[expose] def Lemma39TwoDiscKAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (K' ≤ normalizer (wGroup B V : Set G) →
        ((IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K)) ∨
            CFSG.Open.pRank 2 K ≤ 2) →
        (center (coreQuot K) ≠ ⊥ ∨ ¬ (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected ∨
          ∀ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
            orderOf z ≠ 2) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∃ M : Subgroup (coreQuot K'), Assembly.Dichotomy.dichotomyStronglyEmbedded M) →
        (∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        (∀ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
          orderOf z ≠ 2) →
        K' ≤ normalizer (wGroup B V : Set G))

theorem lemma39TwoDiscIAt_of_K (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) {R : SigOrientation}
    (h : Lemma39TwoDiscKAt R) : Lemma39TwoDiscIAt R := by
  intro G _ _ hG N hN hr K K' V B hP hR hW
  obtain ⟨h1, h2⟩ := h G hG N hN hr K K' V B hP hR hW
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  refine ⟨fun hK'H hcase hdisc => ?_, fun hSE hdisc' => ?_⟩
  · have hcase' : (IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K)) ∨
        CFSG.Open.pRank 2 K ≤ 2 := hcase.symm
    by_cases hhub : center (coreQuot K) = ⊥ ∧
        (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected ∧
        ∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
          orderOf z = 2
    · obtain ⟨hZ, hc, z, hz, hz2⟩ := hhub
      obtain ⟨b, hb2, hbQ', hbQ, hbV, hbE⟩ := exists_vhub hK hK' hz hz2 hV hVK' hE hEK hEV
      exact le_normalizer_wGroup_of_hub hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN hb2 (not_mem_of_center_eq_bot hZ hb2 hbQ) hbQ' hbQ hbV hbE hc
    · refine h1 hK'H hcase' ?_ hdisc
      by_cases hZ : center (coreQuot K) = ⊥
      · by_cases hc : (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected
        · exact Or.inr (Or.inr fun z hz hz2 => hhub ⟨hZ, hc, z, hz, hz2⟩)
        · exact Or.inr (Or.inl hc)
      · exact Or.inl hZ
  · by_cases h3b : ∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
        orderOf z = 2
    · obtain ⟨z, hz, hz2⟩ := h3b
      obtain ⟨b, hb2, hbQ', hbQ, hbV, hbE⟩ := exists_vhub hK hK' hz hz2 hV hVK' hE hEK hEV
      exact le_normalizer_wGroup_of_vhub hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN hb2 hbQ hbQ' hbV hbE
    · exact h2 hSE hdisc' fun z hz hz2 => h3b ⟨z, hz, hz2⟩

end CFSG.ComponentClassification.Sol76.Sig
