module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL310

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G]

@[expose] def SigPair (N K K' V B : Subgroup G) : Prop :=
  K ∈ kStarComponents N ∧ K' ∈ kStarComponents N ∧ K ≠ K' ∧ IsKleinFour V ∧ V ≤ K' ∧
    B ≤ coreActionKernel K' ∧ B ≤ centralizer (V : Set G) ∧ CFSG.Open.IsElemAbelian 2 B ∧
    Nat.card B = 8 ∧ B ≤ N ∧ ∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K

@[expose] def Lemma39For : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      ∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)

@[expose] def Lemma310bRestFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      (∀ s ∈ K', orderOf s = 2 →
        twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G)) ∧
      ∀ s ∈ K ⊓ centralizer (V : Set G), orderOf s = 2 →
        oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G)

@[expose] def SingleComponentExcludedFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      (∀ K'' ∈ kStarComponents N, ∀ s ∈ K'', orderOf s = 2 →
        twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G)) →
      ∀ M : Subgroup G, IsTwoComponentIn M (normalizer (wGroup B V : Set G)) →
        ¬ ∀ K'' ∈ kStarComponents N, K'' ≤ M

@[expose] def Lemma312For : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      (∀ K'' ∈ kStarComponents N, ∀ s ∈ K'', orderOf s = 2 →
        twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G)) →
      (∀ K'' ∈ kStarComponents N, ∃ M ∈ kStarComponents (normalizer (wGroup B V : Set G)),
        K'' ≤ M ∧ K'' ⊔ oddCoreIn M = M) →
      ∀ K'' ∈ kStarComponents N, ∀ s ∈ K'', orderOf s = 2 →
        centralizer ({s} : Set G) ≤ normalizer (wGroup B V : Set G)

@[expose] def SigPairExistsFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ e ∈ K, orderOf e = 2 → ∀ f ∈ K', orderOf f = 2 → f * e = e * f →
      ∃ V B : Subgroup G, (SigPair N K K' V B ∧ f ∈ V ∧ e ∈ B) ∨
        (SigPair N K' K V B ∧ e ∈ V ∧ f ∈ B)

theorem twoLayerIn_centralizer_le_of_rest (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G) {N : Subgroup G}
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hKH : ∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G))
    (hR : ∀ s ∈ K', orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G))
    (hO : ∀ s ∈ K ⊓ centralizer (V : Set G), orderOf s = 2 →
      oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G))
    {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N) {s : G} (hs : s ∈ K'')
    (hs2 : orderOf s = 2) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, -, E, hE, hEB, hEK⟩ := hP
  by_cases h1 : K'' = K
  · exact twoLayerIn_centralizer_le_of_mem_kStar_left hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
      hB8 hE hEB hEK (hKH K hK) (hKH K' hK') hO (h1 ▸ hs) hs2
  by_cases h2 : K'' = K'
  · exact hR s (h2 ▸ hs) hs2
  exact twoLayerIn_centralizer_le_of_mem_kStar_third hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
    hB8 hE hEB hEK (hKH K hK) (hKH K' hK') hK'' h1 h2 (hKH K'' hK'') hs hs2

theorem wGroup_eq_bot_of_inputs (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39For) (h310 : Lemma310bRestFor) (h312 : Lemma312For)
    (hsingle : SingleComponentExcludedFor) (hG : SimpleAmbient G) {N : Subgroup G}
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B) :
    wGroup B V = ⊥ := by
  by_contra hW
  have hKH := h39 G hG N hN K K' V B hP hW
  obtain ⟨hR, hO⟩ := h310 G hG N hN K K' V B hP hW hKH
  have hLH : ∀ K'' ∈ kStarComponents N, ∀ s ∈ K'', orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) :=
    fun _ hK'' _ hs hs2 => twoLayerIn_centralizer_le_of_rest hq hR1 hG hN hP hKH hR hO hK'' hs hs2
  rcases cover_or_single hq hR1 hG hN hKH hLH with hcov | ⟨M, hM, hMK⟩
  · exact false_of_cover hq hF hG hN hcov (h312 G hG N hN K K' V B hP hW hKH hLH hcov)
  · exact hsingle G hG N hN K K' V B hP hW hKH hLH M hM hMK

theorem oddCoreIn_inf_le_wGroup {V B : Subgroup G} (hV : IsKleinFour V)
    (hBV : B ≤ centralizer (V : Set G)) {e f : G} (heB : e ∈ B) (he1 : e ≠ 1) (hfV : f ∈ V) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) ≤
      wGroup B V := by
  have h1 : oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) ≤
      theta (zpowers f) e := by
    rw [theta, centralizer_zpowers_eq]
    exact le_sup_right
  exact h1.trans ((theta_mono (zpowers_le.mpr hfV) (isPGroup_of_isKleinFour hV)
    (comm_of_isKleinFour hV) (le_centralizer_singleton_of_mem hBV heB)).trans
      (theta_le_wGroup heB he1))

theorem lemma315bInputFor_simple_of_inputs (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39For) (h310 : Lemma310bRestFor) (h312 : Lemma312For)
    (hsingle : SingleComponentExcludedFor) (hpair : SigPairExistsFor) :
    Lemma315bInputFor simpleAmbient := by
  refine lemma315bInputFor_of_separated (lemma32FullFor_simple_of_twoPart hq hR1) ?_
  intro G _ _ hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he2; norm_num at he2
  have hf1 : f ≠ 1 := fun h => by rw [h, orderOf_one] at hf2; norm_num at hf2
  obtain ⟨V, B, hVB | hVB⟩ := hpair G hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe
  · obtain ⟨hP, hfV, heB⟩ := hVB
    have hW := wGroup_eq_bot_of_inputs hq hR1 hF h39 h310 h312 hsingle hG hN hP
    exact eq_bot_iff.mpr ((oddCoreIn_inf_le_wGroup hP.2.2.2.1 hP.2.2.2.2.2.2.1 heB he1
      hfV).trans hW.le)
  · obtain ⟨hP, heV, hfB⟩ := hVB
    have hW := wGroup_eq_bot_of_inputs hq hR1 hF h39 h310 h312 hsingle hG hN hP
    rw [inf_comm]
    exact eq_bot_iff.mpr ((oddCoreIn_inf_le_wGroup hP.2.2.2.1 hP.2.2.2.2.2.2.1 hfB hf1
      heV).trans hW.le)

end CFSG.ComponentClassification.Sol76.Sig
