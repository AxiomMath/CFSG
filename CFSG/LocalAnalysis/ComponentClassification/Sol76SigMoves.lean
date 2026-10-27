module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigExt

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

omit [Finite G] in
theorem wGroup_mono_left {E B U : Subgroup G} (hEB : E ≤ B) : wGroup E U ≤ wGroup B U :=
  iSup₂_le fun _ he => iSup_le fun he1 => theta_le_wGroup (hEB he) he1

theorem wGroup_zpowers_le_wGroup {E B V : Subgroup G} (hEB : E ≤ B) (hV : IsKleinFour V)
    (hBV : B ≤ centralizer (V : Set G)) {t : G} (htV : t ∈ V) :
    wGroup E (zpowers t) ≤ wGroup B V :=
  iSup₂_le fun _ he => iSup_le fun he1 =>
    (theta_mono (zpowers_le.mpr htV) (isPGroup_of_isKleinFour hV) (Sig.comm_of_isKleinFour hV)
      (le_centralizer_singleton_of_mem hBV (hEB he))).trans (theta_le_wGroup (hEB he) he1)

omit [Finite G] in
theorem oddCoreIn_inf_le_wGroup_zpowers {E : Subgroup G} {e f : G} (heE : e ∈ E) (he1 : e ≠ 1) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) ≤
      wGroup E (zpowers f) := by
  refine le_trans ?_ (theta_le_wGroup heE he1)
  rw [theta, Sig.centralizer_zpowers_eq]
  exact le_sup_right

theorem wGroup_eq_bot_of_twoConnected (h32 : Lemma32FullFor simpleAmbient)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {V E : Subgroup G} (hV : IsKleinFour V)
    (hVK' : V ≤ K') (h3 : 3 ≤ CFSG.Open.pRank 2 K)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F)
    (hW : ∀ B : Subgroup G, SigPair N K K' V B → wGroup B V = ⊥) : wGroup E V = ⊥ := by
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have h3' : 3 ≤ CFSG.Open.pRank 2 (K ⊓ centralizer (V : Set G)) :=
    h3.trans (pRank_le_of_sup_oddCoreIn inf_le_left
      (inf_centralizer_sup_oddCoreIn_eq (isPGroup_of_isKleinFour hV) hVQ))
  obtain ⟨A, hAX, hA2, hA8⟩ := exists_sq_eq_one_card_eight_le h3'
  obtain ⟨F, hF, hFA⟩ := FooteLit.exists_isKleinFour_le hA2 (by rw [hA8]; norm_num)
  have hAK : A ≤ K := hAX.trans inf_le_left
  have hP : SigPair N K K' V A :=
    ⟨hK, hK', hne, hV, hVK', hAK.trans (le_coreActionKernel_of_ne hK' hK hne.symm),
      hAX.trans inf_le_right, ⟨FooteLit.isMulCommutative_of_sq_eq_one hA2, hA2⟩, hA8,
      hAK.trans (le_of_mem_kStarComponents hK), F, hF, hFA, hFA.trans hAK⟩
  rw [← wGroup_eq_of_reflTransGen h32 hG hN hK hK' hne hV hVK' (hconn F hF (hFA.trans hAX))]
  exact eq_bot_iff.mpr ((wGroup_mono_left hFA).trans (hW A hP).le)

theorem oddCoreIn_inf_eq_bot_of_twoConnected (h32 : Lemma32FullFor simpleAmbient)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {V E : Subgroup G} (hV : IsKleinFour V)
    (hVK' : V ≤ K') (hEX : E ≤ K ⊓ centralizer (V : Set G)) (h3 : 3 ≤ CFSG.Open.pRank 2 K)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F)
    (hW : ∀ B : Subgroup G, SigPair N K K' V B → wGroup B V = ⊥) {e f : G} (heE : e ∈ E)
    (he1 : e ≠ 1) (hfV : f ∈ V) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥ :=
  eq_bot_iff.mpr ((oddCoreIn_inf_le_wGroup hV (hEX.trans inf_le_right) heE he1 hfV).trans
    (wGroup_eq_bot_of_twoConnected h32 hG hN hK hK' hne hV hVK' h3 hconn hW).le)

theorem wGroup_zpowers_eq_bot_of_preconnected (h32 : Lemma32FullFor simpleAmbient)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {E : Subgroup G} (hE : IsKleinFour E)
    (hEK : E ≤ K)
    (hconn : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected)
    {t t' : G} (ht : t ∈ K' ⊓ centralizer (E : Set G)) (ht2 : orderOf t = 2)
    (ht' : t' ∈ K' ⊓ centralizer (E : Set G)) (ht'2 : orderOf t' = 2)
    (h : wGroup E (zpowers t') = ⊥) : wGroup E (zpowers t) = ⊥ := by
  have hr := wGroup_zpowers_eq_of_reachable h32 hG hN hK hK' hne hE hEK
    (hconn ⟨⟨t, ht⟩, by rw [Subgroup.orderOf_mk]; exact ht2⟩
      ⟨⟨t', ht'⟩, by rw [Subgroup.orderOf_mk]; exact ht'2⟩)
  exact hr.trans h

theorem oddCoreIn_inf_eq_bot_of_preconnected (h32 : Lemma32FullFor simpleAmbient)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {E : Subgroup G} (hE : IsKleinFour E)
    (hEK : E ≤ K)
    (hconn : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected)
    {t x : G} (ht : t ∈ K' ⊓ centralizer (E : Set G)) (ht2 : orderOf t = 2) (hxN : x ∈ N)
    (hxQ : x ∈ coreActionKernel K') (hx2 : orderOf x = 2) (hxE : x ∉ E)
    (hEx : E ≤ centralizer ({x} : Set G)) (hxt : x * t = t * x)
    (hW : ∀ V B : Subgroup G, SigPair N K K' V B → wGroup B V = ⊥) {e f : G} (heE : e ∈ E)
    (he1 : e ≠ 1) (hf : f ∈ K' ⊓ centralizer (E : Set G)) (hf2 : orderOf f = 2) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥ := by
  have hEt : E ≤ centralizer ({t} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ht.2 w hw)
  obtain ⟨V, hP, htV⟩ :=
    exists_sigPair_of_isKleinFour hK hK' hne hE hEK ht.1 ht2 hEt hxN hxQ hx2 hxE hEx hxt
  have hWt : wGroup E (zpowers t) = ⊥ := eq_bot_iff.mpr
    ((wGroup_zpowers_le_wGroup le_sup_left hP.2.2.2.1 hP.2.2.2.2.2.2.1 htV).trans
      (hW V _ hP).le)
  have hWf := wGroup_zpowers_eq_bot_of_preconnected h32 hG hN hK hK' hne hE hEK hconn hf hf2
    ht ht2 hWt
  exact eq_bot_iff.mpr ((oddCoreIn_inf_le_wGroup_zpowers heE he1).trans hWf.le)

end CFSG.ComponentClassification.Sol76.Sig
