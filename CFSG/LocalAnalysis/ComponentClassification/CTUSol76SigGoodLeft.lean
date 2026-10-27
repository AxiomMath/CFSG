module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGoodRight

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

omit [Finite G] in
theorem sigPair_of_le_centralizer_right {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    {U : Subgroup G} (hU : IsKleinFour U) (hUY : U ≤ K' ⊓ centralizer (B : Set G)) :
    SigPair N K K' U B := by
  obtain ⟨hK, hK', hne, -, -, hBQ, -, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  refine ⟨hK, hK', hne, hU, hUY.trans inf_le_left, hBQ, fun b hb => mem_centralizer_iff.mpr
    fun u hu => ((mem_centralizer_iff.mp (hUY hu).2) b hb).symm, hB, hB8, hBN, E, hE, hEB, hEK⟩

theorem wGroup_eq_of_le_centralizer_right' (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {U : Subgroup G} (hU : IsKleinFour U)
    (hUY : U ≤ K' ⊓ centralizer (B : Set G)) : wGroup B U = wGroup B V := by
  have hPU := sigPair_of_le_centralizer_right hP hU hUY
  obtain ⟨hK, hK', hne, -, hUK', hBQ, hBU, hB, -, -, E, hE, hEB, hEK⟩ := hPU
  exact (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hU hUK' hBQ hBU hB hE hEB hEK hE
    hEB).symm.trans (wGroup_eq_of_le_centralizer_right hq hR1 hG hN hP hK'W hE hEB hEK hU hUY)

theorem isGoodFor_of_reflTransGen_left (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    {E : Subgroup G} (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K) {F : Subgroup G}
    (hEF : Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) {x : G}
    (hxF : x ∈ F) (hx1 : x ≠ 1) : IsGoodFor N (wGroup B V) x := by
  classical
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, -, -, -⟩ := hP'
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hKQ : K ≤ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK (Ne.symm hne)
  induction hEF generalizing x with
  | refl => exact ⟨hx1, K, K', V, B, hP, rfl, Or.inl (hEB hxF)⟩
  | @tail C D hEC hCD ih =>
    by_cases hCD' : C = D
    · subst hCD'
      exact ih hxF hx1
    have hWD : wGroup D V = wGroup B V :=
      (wGroup_eq_of_reflTransGen h32 hG hN hK hK' hne hV hVK' (hEC.tail hCD)).trans hWE
    obtain ⟨hC, hD, hCX, hDX, hCDc⟩ := hCD
    have hCD'' : ¬ C ≤ D := fun hle => hCD' (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hC.card_four, hD.card_four]))
    obtain ⟨c, hcC, hcD⟩ := IsConcreteLE.not_le_iff_exists.mp hCD''
    have hc1 : c ≠ 1 := fun h => hcD (h ▸ D.one_mem)
    have hc2 : orderOf c = 2 := orderOf_eq_two_of_isKleinFour hC hcC hc1
    have hDK : D ≤ K := hDX.trans inf_le_left
    have hcK : c ∈ K := (hCX hcC).1
    obtain ⟨hAe, hA8⟩ := isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hD) hc2 hcD
      (hCDc hcC)
    have hAQ : D ⊔ zpowers c ≤ coreActionKernel K' :=
      sup_le (hDK.trans hKQ) (zpowers_le.mpr (hKQ hcK))
    have hAV : D ⊔ zpowers c ≤ centralizer (V : Set G) :=
      sup_le (hDX.trans inf_le_right) (zpowers_le.mpr (hCX hcC).2)
    have hAN : D ⊔ zpowers c ≤ N := sup_le (hDK.trans hK.1.1) (zpowers_le.mpr (hK.1.1 hcK))
    have hPA : SigPair N K K' V (D ⊔ zpowers c) := ⟨hK, hK', hne, hV, hVK', hAQ, hAV, hAe,
      by rw [hA8, hD.card_four], hAN, D, hD, le_sup_left, hDK⟩
    have hWA : wGroup (D ⊔ zpowers c) V = wGroup D V :=
      (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hAe hD le_sup_left hDK hD
        le_sup_left).symm
    exact ⟨hx1, K, K', V, D ⊔ zpowers c, hPA, hWA.trans hWD, Or.inl (mem_sup_left hxF)⟩

@[expose] def GoodInvolutionsLeftDiscFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ∀ x ∈ K, orderOf x = 2 →
        (∀ g ∈ normalizer (wGroup B V : Set G), ∀ U E F : Subgroup G, IsKleinFour U →
          U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E → E ≤ B → E ≤ K → IsKleinFour F →
          F ≤ K ⊓ centralizer (U : Set G) → g⁻¹ * x * g ∈ F →
          ¬ Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

theorem goodInvolutionsLeftTwoFor_of_disc (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h : GoodInvolutionsLeftDiscFor) :
    GoodInvolutionsLeftTwoFor := by
  classical
  intro G _ _ hG N hN h2 K K' V B hP hW hKH x hx hx2
  by_cases hc : ∃ g ∈ normalizer (wGroup B V : Set G), ∃ U E F : Subgroup G, IsKleinFour U ∧
      U ≤ K' ⊓ centralizer (B : Set G) ∧ IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧ IsKleinFour F ∧
      F ≤ K ⊓ centralizer (U : Set G) ∧ g⁻¹ * x * g ∈ F ∧
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F
  · obtain ⟨g, hg, U, E, F, hU, hUY, hE, hEB, hEK, -, -, hxF, hEF⟩ := hc
    have hg2 : orderOf (g⁻¹ * x * g) = 2 := by rw [orderOf_inv_mul_mul, hx2]
    have hg1 : g⁻¹ * x * g ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hg2; norm_num at hg2
    have hgood := isGoodFor_of_reflTransGen_left hq hR1 hG hN
      (sigPair_of_le_centralizer_right hP hU hUY) hE hEB hEK hEF hxF hg1
    rw [wGroup_eq_of_le_centralizer_right' hq hR1 hG hN hP (hKH K' hP.2.1) hU hUY] at hgood
    exact ⟨g, hg, hgood⟩
  · exact h G hG N hN h2 K K' V B hP hW hKH x hx hx2
      fun g hg U E F hU hUY hE hEB hEK hF hFY hxF hEF =>
        hc ⟨g, hg, U, E, F, hU, hUY, hE, hEB, hEK, hF, hFY, hxF, hEF⟩

@[expose] def Lemma39TwoDiscFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (K' ≤ normalizer (wGroup B V : Set G) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        K' ≤ normalizer (wGroup B V : Set G))

theorem lemma39TwoRestFor_of_disc (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h : Lemma39TwoDiscFor) :
    Lemma39TwoRestFor := by
  classical
  intro G _ _ hG N hN h2 K K' V B hP hW
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, -⟩ := hP'
  have hK'H : K' ≤ normalizer (wGroup B V : Set G) := by
    by_cases hc : ∃ E : Subgroup G, IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧
        (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected
    · obtain ⟨E, hE, hEB, hEK, hconn⟩ := hc
      exact le_normalizer_wGroup_of_preconnected_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
        hB8 hE hEB hEK hconn
    · exact (h G hG N hN h2 K K' V B hP hW).2 fun E hE hEB hEK hconn =>
        hc ⟨E, hE, hEB, hEK, hconn⟩
  refine ⟨fun _ => ?_, fun _ => hK'H⟩
  by_cases hc : ∃ U E : Subgroup G, IsKleinFour U ∧ U ≤ K' ⊓ centralizer (B : Set G) ∧
      IsKleinFour E ∧ E ≤ B ∧ E ≤ K ∧ ∀ F : Subgroup G, IsKleinFour F →
        F ≤ K ⊓ centralizer (U : Set G) →
        Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F
  · obtain ⟨U, E, hU, hUY, hE, hEB, hEK, hconn⟩ := hc
    have hBU : B ≤ centralizer (U : Set G) :=
      (sigPair_of_le_centralizer_right hP hU hUY).2.2.2.2.2.2.1
    have h1 := le_normalizer_wGroup_of_twoConnected_of_mem hq hR1 hG hN hK hK' hne hU
      (hUY.trans inf_le_left) hBQ hBU hB hB8 hE hEB hEK hBN hconn
    rwa [wGroup_eq_of_le_centralizer_right' hq hR1 hG hN hP hK'H hU hUY] at h1
  · exact (h G hG N hN h2 K K' V B hP hW).1 hK'H fun U E hU hUY hE hEB hEK hconn =>
      hc ⟨U, E, hU, hUY, hE, hEB, hEK, hconn⟩

theorem lemma315bInputFor_simple_of_disc_residues (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39TwoDiscFor) (hgood : GoodInvolutionsLeftDiscFor)
    (hC : SingleComponentCatalogFor) (hpair : SigPairExistsTwoFor) :
    Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_left_residues hq hR1 hF (lemma39TwoRestFor_of_disc hq hR1 h39)
    (goodInvolutionsLeftTwoFor_of_disc hq hR1 hgood) hC hpair

end CFSG.ComponentClassification.Sol76.Sig
