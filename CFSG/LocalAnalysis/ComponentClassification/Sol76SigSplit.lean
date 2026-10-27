module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigBalance
public import CFSG.GH74.GLS.TwoThin.Rank
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalKernel
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigThird

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem three_le_pRank_inf_inf_of_three_le (hK : K ∈ kStarComponents N)
    (h3 : 3 ≤ CFSG.Open.pRank 2 K) {e f : G} (heK : e ∈ K) (he2 : orderOf e = 2)
    (hfQ : f ∈ coreActionKernel K) (hf2 : orderOf f = 2) (hfe : f * e = e * f) :
    3 ≤ CFSG.Open.pRank 2 (K ⊓ centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  have hcomm : commutator ↥K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype, hperf]
  have hrank : 3 ≤ CFSG.Assembly.twoRank ↥K := by
    show 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥K)
    rw [← SectionRank.pRank_eq_pRank_top_subgroup]
    exact h3
  have he2' : orderOf (⟨e, heK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact he2
  have hC : 3 ≤ CFSG.Open.pRank 2 (centralizer ({⟨e, heK⟩} : Set ↥K)) :=
    CFSG.Assembly.Dichotomy.tt_two_le_pRank_involution_centralizer hcomm hrank ⟨e, heK⟩ he2'
  have hmap : (centralizer ({⟨e, heK⟩} : Set ↥K)).map K.subtype ≤
      K ⊓ centralizer ({e} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
  have hCe : 3 ≤ CFSG.Open.pRank 2 (K ⊓ centralizer ({e} : Set G)) :=
    hC.trans ((SectionRank.pRank_le_map (by norm_num) K.subtype K.subtype_injective _).trans
      (SectionRank.pRank_mono (by norm_num) hmap))
  set L := K ⊓ centralizer ({e} : Set G) with hL
  have hfC : f ∈ centralizer ({e} : Set G) := mem_centralizer_singleton_iff.mpr hfe
  have hfN : f ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    rw [hL, mem_inf, mem_inf]
    exact and_congr (mem_normalizer_iff.mp (mem_coreActionKernel.mp hfQ).1 h)
      (mem_normalizer_iff.mp (le_normalizer hfC) h)
  have hfQL : f ∈ coreActionKernel L := by
    refine mem_coreActionKernel.mpr ⟨hfN, fun j hj => ?_⟩
    have h1 : j⁻¹ * f⁻¹ * j * f ∈ oddCoreIn K := (mem_coreActionKernel.mp hfQ).2 j hj.1
    have hjC : j ∈ centralizer ({e} : Set G) := hj.2
    have h2 : j⁻¹ * f⁻¹ * j * f ∈ L := mem_inf.mpr
      ⟨map_subtype_le (pPrimeCore 2 ↥K) h1,
        mul_mem (mul_mem (mul_mem (inv_mem hjC) (inv_mem hfC)) hjC) hfC⟩
    exact Sol76.inf_le_oddCoreIn (coprime_card_oddCoreIn K)
      (inf_le_left.trans (le_normalizer_oddCoreIn K)) ⟨h1, h2⟩
  have hP2 : IsPGroup 2 (zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf2, pow_one])
  have hsup := inf_centralizer_sup_oddCoreIn_eq hP2 (zpowers_le.mpr hfQL)
  have hle := pRank_le_of_sup_oddCoreIn inf_le_left hsup
  rw [Sig.centralizer_zpowers_eq] at hle
  exact hCe.trans hle


abbrev SolCond2 (N K' : Subgroup G) : Prop :=
  IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ∧
    2 < CFSG.Open.pRank 2 K' ∧ ¬ IsSolomonI (coreQuot K')

abbrev SolCond3 (K K' : Subgroup G) : Prop :=
  (Nonempty ((coreQuot K ⧸ center (coreQuot K)) ≃* alternatingGroup (Fin 9)) ∧
      Nat.card (center (coreQuot K)) = 2) ∧
    CFSG.Open.StatedClassicalModel (coreQuot K') .PSL 2 7 1

theorem solCond_of_not_solRestricted (h : ¬ solRestricted G N K K') :
    (kStarComponents N).ncard = 2 ∧ (SolCond2 N K' ∨ SolCond3 K K') := by
  by_contra hc
  apply h
  intro hr
  exact ⟨fun h2 => hc ⟨hr, Or.inl h2⟩, fun h3 => hc ⟨hr, Or.inr h3⟩⟩

omit [Finite G] in
theorem isSolomonI_of_aNine {X : Type} [Group X]
    (h : Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 9)) ∧ Nat.card (center X) = 2) :
    IsSolomonI X :=
  Or.inr (Or.inr (Or.inr h))

theorem center_eq_bot_of_pslTwoSeven {X : Type} [Group X] (hX : IsQuasisimple X)
    (h : CFSG.Open.StatedClassicalModel X .PSL 2 7 1) : center X = ⊥ := by
  have hs : IsSimpleGroup X := UnbalancedCorr.isSimpleGroup_of_statedClassicalModel_psl_two h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h1 | h1
  · exact h1
  · exfalso
    have hnt : Nontrivial (X ⧸ center X) := hX.2.1.toNontrivial
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [(QuotientGroup.eq_one_iff a).mpr (h1 ▸ mem_top a),
      (QuotientGroup.eq_one_iff b).mpr (h1 ▸ mem_top b)]

theorem center_ne_bot_of_mem {b : G} (hbK : b ∈ K)
    (hb2 : orderOf b = 2) (hbQ : b ∈ coreActionKernel K) : center (coreQuot K) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hc := mk_mem_center_quot_of_mem_coreActionKernel (y := (⟨b, hbK⟩ : ↥K)) hbQ
  rw [hbot, mem_bot] at hc
  have hmem : (⟨b, hbK⟩ : ↥K) ∈ pPrimeCore 2 ↥K :=
    (QuotientGroup.eq_one_iff _).mp (by rw [← QuotientGroup.mk'_apply]; exact hc)
  have hdvd := (pPrimeCore 2 ↥K).orderOf_dvd_natCard hmem
  rw [Subgroup.orderOf_mk, hb2] at hdvd
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

@[expose] def SolomonQTwoDisconnectedFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
      IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') →
      3 ≤ CFSG.Open.pRank 2 K → IsSolomonI (coreQuot K)

theorem solRestricted_or_of_two (h22a : SolomonQTwoDisconnectedFor) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hR : ¬ solRestricted G N K K') (hR' : ¬ solRestricted G N K' K) : False := by
  obtain ⟨hr, hc⟩ := solCond_of_not_solRestricted hR
  obtain ⟨-, hc'⟩ := solCond_of_not_solRestricted hR'
  rcases hc with h2 | h3 <;> rcases hc' with h2' | h3'
  · exact h2'.2.2 (h22a G hG N hN hr K hK K' hK' hne h2.1 (by have := h2'.2.1; omega))
  · exact h2.2.2 (isSolomonI_of_aNine h3'.1)
  · exact h2'.2.2 (isSolomonI_of_aNine h3.1)
  · have hQq : IsQuasisimple (coreQuot K) := isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
    have h1 := center_eq_bot_of_pslTwoSeven hQq h3'.2
    have h2 := h3.1.2
    rw [h1, Subgroup.card_bot] at h2
    omega

@[expose] def ForcedSharedRankTwoFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    solRestricted G N K K' → solRestricted G N K' K →
    CFSG.Open.pRank 2 K ≤ 2 → CFSG.Open.pRank 2 K' ≤ 2 →
    ∀ e ∈ K, orderOf e = 2 → ∀ f ∈ K', orderOf f = 2 → f * e = e * f →
    ∀ b ∈ K ⊓ K', orderOf b = 2 → b ∈ coreActionKernel K → b ∈ coreActionKernel K' →
      b * e = e * b → b * f = f * b →
      SigForced solRestricted N K K' e f →
      oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer ({f} : Set G)) = ⊥

theorem forcedSeparationTwoFor_of_split (h22a : SolomonQTwoDisconnectedFor)
    (hSp : ForcedSharedRankTwoFor) : ForcedSeparationTwoFor solRestricted := by
  intro G _ _ hG N hN hr K hK K' hK' hne e heK he2 f hfK' hf2 hfe hF
  have hfQ : f ∈ coreActionKernel K := le_coreActionKernel_of_ne hK hK' hne hfK'
  have heQ : e ∈ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK hne.symm heK
  have hY : 3 ≤ CFSG.Open.pRank 2 K → solRestricted G N K K' → False := fun h3 hR =>
    hF.1 hR (Or.inl (exists_sigPair_of_three_le_pRank hK hK' hne heK he2 hfK' hf2 hfe
      (three_le_pRank_inf_inf_of_three_le hK h3 heK he2 hfQ hf2 hfe)))
  have hY' : 3 ≤ CFSG.Open.pRank 2 K' → solRestricted G N K' K → False := fun h3 hR =>
    hF.2 hR (Or.inl (exists_sigPair_of_three_le_pRank hK' hK hne.symm hfK' hf2 heK he2 hfe.symm
      (three_le_pRank_inf_inf_of_three_le hK' h3 hfK' hf2 heQ he2 hfe.symm)))
  rcases exists_involution_or_three_le_of_ncard_eq_two hN hr hK hK' hne with
    ⟨z, hzC, hz2⟩ | ⟨h3K, h3K', -⟩
  ·
    have hzK : z ∈ kStarKernel N := ⟨(sup_le (map_subtype_le _) (map_subtype_le _)) hzC.1, hzC.2⟩
    have heven : Even (Nat.card (kStarKernel N)) := by
      have hdvd := (kStarKernel N).orderOf_dvd_natCard hzK
      rw [hz2] at hdvd
      exact even_iff_two_dvd.mpr hdvd
    obtain ⟨b, hbC, hb2, hbe, hbf⟩ := exists_involution_commute_of_le_normalizer he2 hf2 hfe
      (le_normalizer_kStarKernel N (le_of_mem_kStarComponents hK heK))
      (le_normalizer_kStarKernel N (le_of_mem_kStarComponents hK' hfK')) heven
    have hbN : b ∈ N := hbC.1
    have hbQ : b ∈ coreActionKernel K := kStarKernel_le_coreActionKernel hK hbC
    have hbQ' : b ∈ coreActionKernel K' := kStarKernel_le_coreActionKernel hK' hbC
    have hX : b ∉ K → solRestricted G N K K' → False := fun hbK hR =>
      hF.1 hR (Or.inl (exists_sigPair_of_not_mem hK hK' hne heK he2 hfK' hf2 hfe hbN hbQ hbQ'
        hb2 hbK hbe hbf))
    have hX' : b ∉ K' → solRestricted G N K' K → False := fun hbK' hR =>
      hF.2 hR (Or.inl (exists_sigPair_of_not_mem hK' hK hne.symm hfK' hf2 heK he2 hfe.symm hbN
        hbQ' hbQ hb2 hbK' hbf hbe))
    by_cases hR : solRestricted G N K K'
    · have hbK : b ∈ K := by
        by_contra h
        exact hX h hR
      have h2K : CFSG.Open.pRank 2 K ≤ 2 := by
        by_contra h
        exact hY (by omega) hR
      by_cases hR' : solRestricted G N K' K
      · have hbK' : b ∈ K' := by
          by_contra h
          exact hX' h hR'
        have h2K' : CFSG.Open.pRank 2 K' ≤ 2 := by
          by_contra h
          exact hY' (by omega) hR'
        exact hSp G hG N hN hr K hK K' hK' hne hR hR' h2K h2K' e heK he2 f hfK' hf2 hfe b
          ⟨hbK, hbK'⟩ hb2 hbQ hbQ' hbe hbf hF
      · obtain ⟨-, hc⟩ := solCond_of_not_solRestricted hR'
        rcases hc with hc2 | hc3
        · exact absurd hc2.2.1 (by omega)
        · have hQq : IsQuasisimple (coreQuot K) :=
            isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
          exact (center_ne_bot_of_mem hbK hb2 hbQ (center_eq_bot_of_pslTwoSeven hQq hc3.2)).elim
    · have hR' : solRestricted G N K' K := by
        by_contra h
        exact solRestricted_or_of_two h22a hG hN hK hK' hne hR h
      have hbK' : b ∈ K' := by
        by_contra h
        exact hX' h hR'
      have h2K' : CFSG.Open.pRank 2 K' ≤ 2 := by
        by_contra h
        exact hY' (by omega) hR'
      obtain ⟨-, hc⟩ := solCond_of_not_solRestricted hR
      rcases hc with hc2 | hc3
      · exact absurd hc2.2.1 (by omega)
      · have hQq : IsQuasisimple (coreQuot K') :=
          isQuasisimple_quotient_of_isPComponent hK'.1.1 hK'.1.2
        exact (center_ne_bot_of_mem hbK' hb2 hbQ' (center_eq_bot_of_pslTwoSeven hQq hc3.2)).elim
  ·
    by_cases hR : solRestricted G N K K'
    · exact (hY h3K hR).elim
    · by_cases hR' : solRestricted G N K' K
      · exact (hY' h3K' hR').elim
      · exact (solRestricted_or_of_two h22a hG hN hK hK' hne hR hR').elim

theorem lemma315bInputFor_simple_of_split (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hW : WTrivialFor solRestricted)
    (h22a : SolomonQTwoDisconnectedFor) (hSp : ForcedSharedRankTwoFor) :
    Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_wTrivialFor_two hq hR1 hW
    (forcedSeparationTwoFor_of_split h22a hSp)

end CFSG.ComponentClassification.Sol76.Sig
