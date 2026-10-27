module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39KZ

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G]

@[expose] def SolRestrictedHub (N K K' : Subgroup G) : Prop :=
  SolRestricted N K K' ∧ ((kStarComponents N).ncard = 2 →
    ¬ ((center (coreQuot K) ≠ ⊥ ∨ (IsSolomonI (coreQuot K) ∧ ¬ IsSolomonI (coreQuot K'))) ∧
      center (coreQuot K') = ⊥ ∧ SolRestricted N K' K))

@[expose] def solRestrictedHub : SigOrientation := fun _ _ _ N K K' => SolRestrictedHub N K K'

theorem solRestrictedHub_le (G : Type) [Group G] [Finite G] (N K K' : Subgroup G)
    (h : solRestrictedHub G N K K') : solRestricted G N K K' :=
  h.1

theorem solRestrictedHub_of_ncard_ne_two {N K K' : Subgroup G}
    (hr : (kStarComponents N).ncard ≠ 2) : solRestrictedHub G N K K' :=
  ⟨solRestricted_of_ncard_ne_two hr, fun h => absurd h hr⟩

theorem solRestricted_swap_of {N K K' : Subgroup G}
    (hK : ¬ (2 < CFSG.Open.pRank 2 K ∧ ¬ IsSolomonI (coreQuot K)))
    (hZ' : center (coreQuot K') = ⊥) : solRestricted G N K' K := by
  intro _
  refine ⟨fun h2 => hK ⟨h2.2.1, h2.2.2⟩, fun h3 => ?_⟩
  have h := h3.1.2
  rw [hZ', Subgroup.card_bot] at h
  exact absurd h (by norm_num)

theorem solRestrictedHub_swap {N K K' : Subgroup G} (hR : solRestricted G N K K')
    (hRH : ¬ solRestrictedHub G N K K') :
    (kStarComponents N).ncard = 2 ∧ center (coreQuot K') = ⊥ ∧ solRestrictedHub G N K' K := by
  have h : (kStarComponents N).ncard = 2 ∧
      ((center (coreQuot K) ≠ ⊥ ∨ (IsSolomonI (coreQuot K) ∧ ¬ IsSolomonI (coreQuot K'))) ∧
        center (coreQuot K') = ⊥ ∧ SolRestricted N K' K) := by
    by_contra hn
    exact hRH ⟨hR, fun hr h3 => hn ⟨hr, h3⟩⟩
  obtain ⟨hr, hcase, hZ', hR'⟩ := h
  refine ⟨hr, hZ', hR', fun _ h3 => ?_⟩
  obtain ⟨hc, hZ, -⟩ := h3
  rcases hc with hZ'1 | ⟨hI', -⟩
  · exact hZ'1 hZ'
  · rcases hcase with hZn | ⟨-, hI'n⟩
    · exact hZn hZ
    · exact hI'n hI'

theorem sigEscape_of_center_eq_bot {N K K' : Subgroup G} (hN : IsSolomonChoice N)
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {e f : G} (heK : e ∈ K) (he2 : orderOf e = 2)
    (hfK' : f ∈ K') (hf2 : orderOf f = 2) (hfe : f * e = e * f)
    (hZ' : center (coreQuot K') = ⊥) : SigEscape N K' K f e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heQ : e ∈ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK hne.symm heK
  left
  rcases exists_involution_or_three_le_of_ncard_eq_two hN hr hK hK' hne with
    ⟨z, hzC, hz2⟩ | ⟨-, h3K', -⟩
  · have hzK : z ∈ kStarKernel N :=
      ⟨(sup_le (map_subtype_le _) (map_subtype_le _)) hzC.1, hzC.2⟩
    have heven : Even (Nat.card (kStarKernel N)) := by
      have hdvd := (kStarKernel N).orderOf_dvd_natCard hzK
      rw [hz2] at hdvd
      exact even_iff_two_dvd.mpr hdvd
    obtain ⟨b, hbC, hb2, hbe, hbf⟩ := exists_involution_commute_of_le_normalizer he2 hf2 hfe
      (le_normalizer_kStarKernel N (le_of_mem_kStarComponents hK heK))
      (le_normalizer_kStarKernel N (le_of_mem_kStarComponents hK' hfK')) heven
    have hbQ : b ∈ coreActionKernel K := kStarKernel_le_coreActionKernel hK hbC
    have hbQ' : b ∈ coreActionKernel K' := kStarKernel_le_coreActionKernel hK' hbC
    have hbK' : b ∉ K' := by
      intro hbK'
      have h1 := mk_mem_center_of_mem_coreActionKernel (u := ⟨b, hbK'⟩) hbQ'
      rw [hZ', mem_bot] at h1
      have hbO : b ∈ oddCoreIn K' := mk_eq_one_iff.mp h1
      have hO : Odd (Nat.card (oddCoreIn K')) :=
        Nat.coprime_two_left.mp (coprime_card_oddCoreIn K')
      have hdvd := (oddCoreIn K').orderOf_dvd_natCard hbO
      rw [hb2] at hdvd
      exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)
    exact exists_sigPair_of_not_mem hK' hK hne.symm hfK' hf2 heK he2 hfe.symm hbC.1 hbQ' hbQ
      hb2 hbK' hbf hbe
  · exact exists_sigPair_of_three_le_pRank hK' hK hne.symm hfK' hf2 heK he2 hfe.symm
      (three_le_pRank_inf_inf_of_three_le hK' h3K' hfK' hf2 heQ he2 hfe.symm)

theorem forcedSeparationTwoFor_hub (h : ForcedSeparationTwoFor solRestricted) :
    ForcedSeparationTwoFor solRestrictedHub := by
  intro G _ _ hG N hN hr K hK K' hK' hne e heK he2 f hfK' hf2 hfe hF
  refine h G hG N hN hr K hK K' hK' hne e heK he2 f hfK' hf2 hfe ⟨fun hR => ?_, fun hR' => ?_⟩
  · by_cases hRH : solRestrictedHub G N K K'
    · exact hF.1 hRH
    · obtain ⟨-, hZ', hRH'⟩ := solRestrictedHub_swap hR hRH
      exact (hF.2 hRH' (sigEscape_of_center_eq_bot hN hr hK hK' hne heK he2 hfK' hf2 hfe
        hZ')).elim
  · by_cases hRH' : solRestrictedHub G N K' K
    · exact hF.2 hRH'
    · obtain ⟨-, hZ, hRH⟩ := solRestrictedHub_swap hR' hRH'
      exact (hF.1 hRH (sigEscape_of_center_eq_bot hN hr hK' hK hne.symm hfK' hf2 heK he2
        hfe.symm hZ)).elim

section Graph

variable {X : Type} [Group X]

theorem involutionGraph_preconnected_of_mem_center {τ : X} (hτ : τ ∈ center X)
    (hτ2 : orderOf τ = 2) : (CFSG.Assembly.involutionGraph X).Preconnected := by
  have key : ∀ u : {t : X // orderOf t = 2},
      (CFSG.Assembly.involutionGraph X).Reachable u ⟨τ, hτ2⟩ := by
    intro u
    by_cases hu : u = ⟨τ, hτ2⟩
    · subst hu
      exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [CFSG.Assembly.involutionGraph, SimpleGraph.fromRel_adj]
      exact ⟨hu, Or.inl ((mem_center_iff.mp hτ) (u : X))⟩
  intro u v
  exact (key u).trans (key v).symm

variable [Finite X]

theorem exists_orderOf_eq_two_mem_center (hO : pPrimeCore 2 X = ⊥) (hZ : center X ≠ ⊥) :
    ∃ τ ∈ center X, orderOf τ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (center X) := by
    by_contra h
    exact hZ ((pPrimeCore_eq_bot_iff.mp hO) (center X) inferInstance
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h))
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' (G := center X) 2 h2
  exact ⟨τ, τ.2, by rw [Subgroup.orderOf_coe]; exact hτ⟩

theorem isSolomonI_of_not_preconnected (hq : IsQuasisimple X)
    (hZ : center X = ⊥) (hc : ¬ (CFSG.Assembly.involutionGraph X).Preconnected) :
    IsSolomonI X := by
  let e : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have hs : IsSimpleGroup X := e.symm.isSimpleGroup
  have heven : Even (Nat.card X) := by
    by_contra hodd
    apply hc
    intro u
    exfalso
    have hdvd := orderOf_dvd_natCard (u : X)
    rw [u.2] at hdvd
    exact hodd (even_iff_two_dvd.mpr hdvd)
  obtain ⟨M, hM⟩ :=
    (CFSG.Assembly.Dichotomy.involutionGraph_disconnected_iff_stronglyEmbedded X heven).mp hc
  have hM' : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
    refine ⟨hM.1, hM.2.1, fun g hg => ?_⟩
    have h := hM.2.2 g⁻¹ (fun h => hg (by simpa using M.inv_mem h))
    rwa [inv_inv] at h
  have hB : CFSG.Open.fusionIsBenderGroup X :=
    CFSG.Open.fusionIsBenderGroup_of_isBenderGroup (CFSG.Milestones.bender_suzuki M hM')
  refine Or.inr (Or.inr (Or.inl ?_))
  rcases hB with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans e'⟩⟩)

end Graph

@[expose] def Lemma39TwoDiscKCAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
        orderOf z = 2) →
      ¬ (IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)) ∧
          IsInvolutionCoreFree (coreQuot K' ⧸ center (coreQuot K'))) →
      center (coreQuot K') ≠ ⊥ →
      (center (coreQuot K) ≠ ⊥ → ∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
        ∀ b : G, orderOf b = 2 → b ∈ coreActionKernel K → b ∈ coreActionKernel K' →
          b ∈ centralizer (V : Set G) → b ∈ centralizer (E : Set G) → b ∈ K) →
      K' ≤ normalizer (wGroup B V : Set G) →
        ((IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K)) ∨
            CFSG.Open.pRank 2 K ≤ 2) →
        (center (coreQuot K) ≠ ⊥ ∨ ¬ (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)

theorem lemma39TwoDiscKZAt_hub_of_KC (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient)
    (hI : ∀ (X : Type) [Group X] [Finite X], IsSolomonI X → IsInvolutionCoreFree (X ⧸ center X))
    (h : Lemma39TwoDiscKCAt solRestrictedHub) : Lemma39TwoDiscKZAt solRestrictedHub := by
  intro G _ _ hG N hN hr K K' V B hP hR hW hz hnboth hK'H hcase hdisc hconn
  by_cases hhub : center (coreQuot K) ≠ ⊥ → ∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
      ∀ b : G, orderOf b = 2 → b ∈ coreActionKernel K → b ∈ coreActionKernel K' →
        b ∈ centralizer (V : Set G) → b ∈ centralizer (E : Set G) → b ∈ K
  · refine h G hG N hN hr K K' V B hP hR hW hz hnboth ?_ hhub hK'H hcase hdisc hconn
    have hK : K ∈ kStarComponents N := hP.1
    intro hZ'
    refine hR.2 hr ⟨?_, hZ', solRestricted_swap_of ?_ hZ'⟩
    · by_cases hZ : center (coreQuot K) = ⊥
      · have hc : ¬ (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected := by
          rcases hdisc with h1 | h1
          · exact absurd hZ h1
          · exact h1
        have hKI : IsSolomonI (coreQuot K) := isSolomonI_of_not_preconnected
          (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2) hZ hc
        exact Or.inr ⟨hKI, fun hK'I => hnboth ⟨hI _ hKI, hI _ hK'I⟩⟩
      · exact Or.inl hZ
    · rintro ⟨h2, hnI⟩
      rcases hcase with ⟨-, hKI⟩ | hle
      · exact hnI hKI
      · omega
  · push Not at hhub
    obtain ⟨hZ, E, hE, hEB, hEK, b, hb2, hbQ, hbQ', hbV, hbE, hbK⟩ := hhub
    obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, -⟩ := hP
    obtain ⟨τ, hτ, hτ2⟩ := exists_orderOf_eq_two_mem_center
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2) hZ
    exact le_normalizer_wGroup_of_hub hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB hEK
      hBN hb2 hbK hbQ' hbQ hbV hbE (involutionGraph_preconnected_of_mem_center hτ hτ2)

end CFSG.ComponentClassification.Sol76.Sig
