module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGoodLeft
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigRestrict

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

@[expose] def Lemma39TwoDiscAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (K' ≤ normalizer (wGroup B V : Set G) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        K' ≤ normalizer (wGroup B V : Set G))

@[expose] def GoodInvolutionsLeftDiscAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ∀ x ∈ K, orderOf x = 2 →
        (∀ g ∈ normalizer (wGroup B V : Set G), ∀ U E F : Subgroup G, IsKleinFour U →
          U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E → E ≤ B → E ≤ K → IsKleinFour F →
          F ≤ K ⊓ centralizer (U : Set G) → g⁻¹ * x * g ∈ F →
          ¬ Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

theorem lemma39TwoDiscAt_of_for (h : Lemma39TwoDiscFor) (R : SigOrientation) :
    Lemma39TwoDiscAt R :=
  fun G _ _ hG N hN h2 K K' V B hP _ hW => h G hG N hN h2 K K' V B hP hW

theorem goodInvolutionsLeftDiscAt_of_for (h : GoodInvolutionsLeftDiscFor) (R : SigOrientation) :
    GoodInvolutionsLeftDiscAt R :=
  fun G _ _ hG N hN h2 K K' V B hP _ hW => h G hG N hN h2 K K' V B hP hW

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem wGroup_eq_bot_of_disc (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (hC : SingleComponentCatalogFor) {R : SigOrientation} (h39 : Lemma39TwoDiscAt R)
    (hgood : GoodInvolutionsLeftDiscAt R) (hG : SimpleAmbient G) (hN : IsSolomonChoice N)
    {K K' V B : Subgroup G} (hP : SigPair N K K' V B) (hR : R G N K K') : wGroup B V = ⊥ := by
  classical
  by_contra hW
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E₀, hE₀, hE₀B, hE₀K⟩ := hP'
  set H := normalizer (wGroup B V : Set G) with hH
  have hK'H : K' ≤ H := by
    by_cases h2 : (kStarComponents N).ncard = 2
    · by_cases hc : ∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧
          (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected
      · obtain ⟨E, hE, hEB, hEK, hconn⟩ := hc
        exact le_normalizer_wGroup_of_preconnected_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV
          hB hB8 hE hEB hEK hconn
      · exact (h39 G hG N hN h2 K K' V B hP hR hW).2 fun E hE hEB hEK hconn =>
          hc ⟨E, hE, hEB, hEK, hconn⟩
    · obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := exists_third_kStar_of_ncard_ne_two hK hK' hne h2
      exact le_normalizer_wGroup_of_third_right hq hR1 hG hN hP hK₃ hK₃K hK₃K'
  have hKH₀ : K ≤ H := by
    by_cases h2 : (kStarComponents N).ncard = 2
    · by_cases hc : ∃ U E : Subgroup G, IsKleinFour U ∧ U ≤ K' ⊓ centralizer (B : Set G) ∧
          IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧ ∀ F : Subgroup G, IsKleinFour F →
            F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F
      · obtain ⟨U, E, hU, hUY, hE, hEB, hEK, hconn⟩ := hc
        have hBU : B ≤ centralizer (U : Set G) :=
          (sigPair_of_le_centralizer_right hP hU hUY).2.2.2.2.2.2.1
        have h1 := le_normalizer_wGroup_of_twoConnected_of_mem hq hR1 hG hN hK hK' hne hU
          (hUY.trans inf_le_left) hBQ hBU hB hB8 hE hEB hEK hBN hconn
        rwa [wGroup_eq_of_le_centralizer_right' hq hR1 hG hN hP hK'H hU hUY] at h1
      · exact (h39 G hG N hN h2 K K' V B hP hR hW).1 hK'H fun U E hU hUY hE hEB hEK hconn =>
          hc ⟨U, E, hU, hUY, hE, hEB, hEK, hconn⟩
    · obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := exists_third_kStar_of_ncard_ne_two hK hK' hne h2
      exact le_normalizer_wGroup_of_third hq hR1 hG hN hP hK₃ hK₃K hK₃K'
  have hKH : ∀ K'' ∈ kStarComponents N, K'' ≤ H := by
    intro K'' hK''
    by_cases hK''K : K'' = K
    · exact hK''K ▸ hKH₀
    by_cases hK''K' : K'' = K'
    · exact hK''K' ▸ hK'H
    exact le_normalizer_wGroup_of_ne_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE₀ hE₀B
      hE₀K hBN hK'' hK''K hK''K'
  have hgoodAll : ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
      ∃ g ∈ H, IsGoodFor N (wGroup B V) (g⁻¹ * x * g) := by
    intro K'' hK'' x hx hx2
    by_cases h2 : (kStarComponents N).ncard = 2
    · by_cases hK''K : K'' = K
      · rw [hK''K] at hx
        by_cases hc : ∃ g ∈ H, ∃ U E F : Subgroup G, IsKleinFour U ∧
            U ≤ K' ⊓ centralizer (B : Set G) ∧ IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧ IsKleinFour F ∧
            F ≤ K ⊓ centralizer (U : Set G) ∧ g⁻¹ * x * g ∈ F ∧
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F
        · obtain ⟨g, hg, U, E, F, hU, hUY, hE, hEB, hEK, -, -, hxF, hEF⟩ := hc
          have hg2 : orderOf (g⁻¹ * x * g) = 2 := by rw [orderOf_inv_mul_mul, hx2]
          have hg1 : g⁻¹ * x * g ≠ 1 := fun h1 => by
            rw [h1, orderOf_one] at hg2
            norm_num at hg2
          have hgd := isGoodFor_of_reflTransGen_left hq hR1 hG hN
            (sigPair_of_le_centralizer_right hP hU hUY) hE hEB hEK hEF hxF hg1
          rw [wGroup_eq_of_le_centralizer_right' hq hR1 hG hN hP hK'H hU hUY] at hgd
          exact ⟨g, hg, hgd⟩
        · exact hgood G hG N hN h2 K K' V B hP hR hW hKH x hx hx2
            fun g hg U E F hU hUY hE hEB hEK hF hFY hxF hEF =>
              hc ⟨g, hg, U, E, F, hU, hUY, hE, hEB, hEK, hF, hFY, hxF, hEF⟩
      by_cases hK''K' : K'' = K'
      · rw [hK''K'] at hx
        obtain ⟨g, hg, hgd⟩ := exists_isGoodFor_of_mem_right_all hq hR1 hG hN hP hK'H hx hx2
        exact ⟨g, hK'H hg, hgd⟩
      exfalso
      have hsub : ({K'', K, K'} : Set (Subgroup G)) ⊆ kStarComponents N := by
        rintro J (rfl | rfl | rfl)
        · exact hK''
        · exact hK
        · exact hK'
      have h3 : ({K'', K, K'} : Set (Subgroup G)).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair hne]
        simp [hK''K, hK''K']
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    · obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := exists_third_kStar_of_ncard_ne_two hK hK' hne h2
      refine ⟨1, one_mem _, ?_⟩
      rw [inv_one, one_mul, mul_one]
      exact isGoodFor_of_third hq hR1 hG hN hP hKH hK₃ hK₃K hK₃K' hK'' hx hx2
  have hfacts : ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
      twoLayerIn (centralizer ({x} : Set G)) ≤ H ∧ oddCoreIn (centralizer ({x} : Set G)) ≤ H ∧
        oddCoreIn H ⊓ centralizer ({x} : Set G) ≤ oddCoreIn (centralizer ({x} : Set G)) := by
    intro K'' hK'' x hx hx2
    obtain ⟨g, hg, hgx⟩ := hgoodAll K'' hK'' x hx hx2
    exact good_facts_of_conj hg (good_facts hq hR1 hG hN hKH hgx)
  have hLH : ∀ K'' ∈ kStarComponents N, ∀ x ∈ K'', orderOf x = 2 →
      twoLayerIn (centralizer ({x} : Set G)) ≤ H := fun K'' hK'' x hx hx2 =>
    (hfacts K'' hK'' x hx hx2).1
  rcases cover_or_single hq hR1 hG hN hKH hLH with hcov | ⟨M, hM, hMK⟩
  · have hOW := oddCoreIn_normalizer_wGroup_eq hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE₀
      hE₀B hE₀K (hKH K hK) (hKH K' hK')
    have hHO : normalizer (oddCoreIn H : Set G) ≤ H := by rw [hOW]
    exact false_of_cover hq hF hG hN hcov fun K'' hK'' s hs hs2 =>
      centralizer_le_of_cover hq hR1 hG hN hKH hcov hfacts hHO hK'' hs hs2
  · exact singleComponentExcludedFor_of_catalog hq hR1 hC G hG N hN K K' V B hP hW hKH hLH M hM hMK

theorem wTrivialFor_of_disc (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (hC : SingleComponentCatalogFor) {R : SigOrientation} (h39 : Lemma39TwoDiscAt R)
    (hgood : GoodInvolutionsLeftDiscAt R) : WTrivialFor R :=
  fun _ _ _ hG _ hN _ _ _ _ hP hR => wGroup_eq_bot_of_disc hq hR1 hF hC h39 hgood hG hN hP hR

@[expose] def ForcedSeparationTwoFor (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ e ∈ K, orderOf e = 2 → ∀ f ∈ K', orderOf f = 2 → f * e = e * f →
      SigForced R N K K' e f →
      oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥

theorem forcedSeparationFor_of_two (hq : QuasisimpleTwoPartInput) {R : SigOrientation}
    (hR3 : ∀ (G : Type) [Group G] [Finite G] (N K K' : Subgroup G),
      (kStarComponents N).ncard ≠ 2 → R G N K K')
    (h : ForcedSeparationTwoFor R) : ForcedSeparationFor R := by
  intro G _ _ hG N hN K hK K' hK' hne e heK he2 f hfK' hf2 hfe hforced
  by_cases h2 : (kStarComponents N).ncard = 2
  · exact h G hG N hN h2 K hK K' hK' hne e heK he2 f hfK' hf2 hfe hforced
  exfalso
  obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := exists_third_kStar_of_ncard_ne_two hK hK' hne h2
  obtain ⟨V, B, hP, hfV, heB⟩ :=
    exists_sigPair_of_third hq hG hK hK' hne hK₃ hK₃K hK₃K' heK he2 hfK' hf2 hfe
  exact hforced.1 (hR3 G N K K' h2) (Or.inl ⟨V, B, hP, hfV, heB⟩)

theorem lemma315bInputFor_simple_of_orientation (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (hC : SingleComponentCatalogFor) {R : SigOrientation}
    (hR3 : ∀ (G : Type) [Group G] [Finite G] (N K K' : Subgroup G),
      (kStarComponents N).ncard ≠ 2 → R G N K K')
    (h39 : Lemma39TwoDiscAt R) (hgood : GoodInvolutionsLeftDiscAt R)
    (hres : ForcedSeparationTwoFor R) : Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_forced hq hR1 (wTrivialFor_of_disc hq hR1 hF hC h39 hgood)
    (forcedSeparationFor_of_two hq hR3 hres)

theorem lemma315bInputFor_simple_of_solRestricted (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (hC : SingleComponentCatalogFor) (h39 : Lemma39TwoDiscAt solRestricted)
    (hgood : GoodInvolutionsLeftDiscAt solRestricted)
    (hres : ForcedSeparationTwoFor solRestricted) : Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_orientation hq hR1 hF hC
    (fun _ _ _ _ _ _ h2 => fun h2' => absurd h2' h2) h39 hgood hres

end CFSG.ComponentClassification.Sol76.Sig
