module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76AltClass
public import CFSG.LocalAnalysis.ComponentClassification.Sol76TwoComp
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Transport
public import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Simple

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X]

theorem pRank_le_of_le {H K : Subgroup X} (h : H ≤ K) : CFSG.pRank 2 ↥H ≤ CFSG.pRank 2 ↥K := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
    ← SectionRank.pRank_eq_pRank_top_subgroup, ← SectionRank.pRank_eq_pRank_top_subgroup]
  exact SectionRank.pRank_mono one_lt_two h

theorem ne_bot_of_isPComponent' {G : Type*} [Group G] {p : ℕ} {L : Subgroup G}
    (hL : IsPComponent p L) : L ≠ ⊥ := by
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  intro h
  rw [h, Subgroup.map_bot] at hLK
  subst hLK
  obtain ⟨a, b, hab⟩ := hK.1.2.2
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have : a = b := Subsingleton.elim _ _
  rw [this]

theorem isTwoComponentIn_of_le_normalizer {J N C : Subgroup X}
    (hJ : FooteLit.IsTwoComponentIn J C) (hJN : J ≤ N) (hNJ : N ≤ normalizer (J : Set X)) :
    FooteLit.IsTwoComponentIn J N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJ.1).mp hJ.2
  have hn : (J.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hNJ
  exact ⟨hJN, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J N hJN).mpr
    ⟨hn.isSubnormal, hi.2⟩⟩

theorem mem_solomonKStar_of_isAltTwoComponent (hmax : MaximalityLemmaInput)
    (hS : SolAltLit.SchurAlternatingMultiplierInput) [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hJ : SolAltLit.IsAltTwoComponent t J n) (hn : Odd n) (hn9 : 9 ≤ n)
    (hmaxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n) :
    J ∈ FooteLit.solomonKStar X := by
  have hmem := isSolomonMember_of_isAltTwoComponent hJ
  obtain ⟨e⟩ := hJ.2.2.2
  refine ⟨hmax X hna hK hz hU n hn hn9 ⟨t, J, hJ⟩ hmaxdeg J hmem ⟨e⟩, ?_⟩
  obtain ⟨e'⟩ := nonempty_fusionZStar_equiv_of_coreQuotient (by omega) e
  exact Sol76.isSolomonWide_of_fusionZStar hS hmem (by omega) e'

theorem commutator_conjugate_ne_bot (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X) {t : X}
    {J : Subgroup X} {n : ℕ}
    (hJ : SolAltLit.IsAltTwoComponent t J n) (hn9 : 9 ≤ n) (hJs : J ∈ FooteLit.solomonKStar X)
    (g : X) : ⁅J, conjugate J g⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hc
  obtain ⟨ht, hJC, hJp, ⟨e⟩⟩ := hJ
  have hJtc : FooteLit.IsTwoComponentIn J (centralizer ({t} : Set X)) := ⟨hJC, hJp⟩
  set J' := conjugate J g with hJ'
  set N := J ⊔ J' with hN
  have hcomm : ∀ x ∈ J, ∀ y ∈ J', x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJC hJp
  have hJne : J ≠ ⊥ := fun h => ne_bot_of_isPComponent' hJp (by rw [h]; exact bot_subgroupOf _)
  have hne : J ≠ J' := by
    intro h
    apply hJne
    rw [← hperf]
    nth_rewrite 2 [h]
    exact hc
  have hJ'C : J' ≤ centralizer (J : Set X) := fun y hy =>
    mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy
  have hJC' : J ≤ centralizer (J' : Set X) := fun x hx =>
    mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm
  have hNJ : N ≤ normalizer (J : Set X) :=
    sup_le le_normalizer (hJ'C.trans (centralizer_le_normalizer _))
  have hNJ' : N ≤ normalizer (J' : Set X) :=
    sup_le (hJC'.trans (centralizer_le_normalizer _)) le_normalizer
  have hJN : FooteLit.IsTwoComponentIn J N := isTwoComponentIn_of_le_normalizer hJtc le_sup_left hNJ
  have hJ'tc := Sol76.isTwoComponentIn_map (MulAut.conj g⁻¹) hJtc
  have hJ'N : FooteLit.IsTwoComponentIn J' N :=
    isTwoComponentIn_of_le_normalizer hJ'tc le_sup_right hNJ'
  have hJ's : J' ∈ FooteLit.solomonKStar X := Sol76.conjugate_mem_solomonKStar hJs g
  have e' : J' ⧸ pPrimeCore 2 J' ≃* alternatingGroup (Fin n) :=
    (coreQuotCongr (J.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)).symm.trans e
  have hrJ : 3 ≤ CFSG.pRank 2 J := three_le_pRank_of_coreQuotient (by omega) e
  have hrJ' : 3 ≤ CFSG.pRank 2 J' := three_le_pRank_of_coreQuotient (by omega) e'
  set S : Set (Subgroup X) := {K | FooteLit.IsTwoComponentIn K N ∧ K ∈ FooteLit.solomonKStar X}
    with hSdef
  have hSfin : S.Finite := Set.toFinite S
  set s := hSfin.toFinset with hs
  have hJs' : J ∈ s := hSfin.mem_toFinset.mpr ⟨hJN, hJs⟩
  have hJ's' : J' ∈ s := hSfin.mem_toFinset.mpr ⟨hJ'N, hJ's⟩
  have hr : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨J, hJs', J', hJ's', hne⟩
  set ee := s.equivFin.symm with hee
  set Kf : Fin s.card → Subgroup X := fun i => ((ee i : s) : Subgroup X) with hKf
  have hKfS : ∀ i, Kf i ∈ S := fun i => hSfin.mem_toFinset.mp (ee i).2
  have hbal : FooteLit.IsKBalanced N := by
    refine ⟨s.card, Kf, fun i j hij => ee.injective (Subtype.ext hij), fun K => ⟨fun hK => ?_,
      ?_⟩, hr, fun i j hij => ?_, ?_, ?_⟩
    · refine ⟨ee.symm ⟨K, hSfin.mem_toFinset.mpr hK⟩, ?_⟩
      simp only [hKf, Equiv.apply_symm_apply]
    · rintro ⟨i, rfl⟩
      exact hKfS i
    · exact FooteLit.commutator_le_oddCoreIn_of_ne (hKfS i).1 (hKfS j).1
        (fun h => hij (ee.injective (Subtype.ext h)))
    ·
      refine ⟨ee.symm ⟨J, hJs'⟩, ?_⟩
      have hKi : Kf (ee.symm ⟨J, hJs'⟩) = J := by simp only [hKf, Equiv.apply_symm_apply]
      rw [hKi]
      have hle : J' ≤ (FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N) ⊓ coreActionKernel J :=
        le_inf ((FooteLit.le_twoLayerIn_of_isTwoComponentIn hJ'N).trans le_sup_right)
          fun y hy => mem_coreActionKernel_of_commute fun x hx => hcomm x hx y hy
      exact hrJ'.trans (pRank_le_of_le hle)
    ·
      by_cases h3 : 3 ≤ s.card
      · exact Or.inl h3
      · right; right
        have hsub : ({J, J'} : Finset (Subgroup X)) ⊆ s := by
          intro K hK
          rw [Finset.mem_insert, Finset.mem_singleton] at hK
          rcases hK with rfl | rfl
          · exact hJs'
          · exact hJ's'
        have hseq : ({J, J'} : Finset (Subgroup X)) = s :=
          Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)
        have hgood : ∀ i, 3 ≤ CFSG.pRank 2 ↥(Kf i) ∧ ¬ FooteLit.HasStronglyEmbedded ↥(Kf i) := by
          intro i
          have hi : Kf i ∈ ({J, J'} : Finset (Subgroup X)) := by rw [hseq]; exact (ee i).2
          rw [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with hi | hi
          · rw [hi]
            exact ⟨hrJ, not_hasStronglyEmbedded_of_coreQuotient (by omega) e⟩
          · rw [hi]
            exact ⟨hrJ', not_hasStronglyEmbedded_of_coreQuotient (by omega) e'⟩
        exact ⟨(hgood _).1, (hgood _).1, fun h => (h.elim (hgood _).2 (hgood _).2).elim⟩
  exact h13 X inferInstance hna hK N hbal

theorem le_normalizer_oddCoreIn_sup (h13 : Sol76T13.SolomonThm13Simple)
    (h212 : Sol76.Lemma212Input) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) {t : X} {J : Subgroup X} {n : ℕ}
    (hJ : SolAltLit.IsAltTwoComponent t J n) (hn9 : 9 ≤ n) (hJs : J ∈ FooteLit.solomonKStar X)
    {y : X} (hy : orderOf y = 2) (hJy : J ≤ centralizer ({y} : Set X)) :
    centralizer ({y} : Set X) ≤ normalizer
      ((FooteLit.oddCoreIn (centralizer ({y} : Set X)) ⊔ J : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht, hJC, hJp, ⟨e⟩⟩ := hJ
  have hJtc : FooteLit.IsTwoComponentIn J (centralizer ({t} : Set X)) := ⟨hJC, hJp⟩
  set C := centralizer ({y} : Set X) with hC
  set T := zpowers y with hT
  have hCT : centralizer ((T : Subgroup X) : Set X) = C := by
    rw [hT, zpowers_eq_closure, centralizer_closure]
  have hJmem : FooteLit.IsSolomonMember J := hJs.1.1
  have hperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJC hJp
  have hJne : J ≠ ⊥ := fun h => ne_bot_of_isPComponent' hJp (by rw [h]; exact bot_subgroupOf _)
  have hTne : T ≠ ⊥ := by
    intro h
    rw [hT, zpowers_eq_bot] at h
    rw [h, orderOf_one] at hy
    norm_num at hy
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hTJ : T ≤ coreActionKernel J := by
    rw [hT, zpowers_le]
    exact mem_coreActionKernel_of_commute fun j hj => mem_centralizer_singleton_iff.mp (hJy hj)
  have hJinf : J ⊓ C = J := inf_eq_left.mpr hJy
  have hJlayer : FooteLit.twoLayerIn J = J := Sol76.twoLayerIn_eq_self_of_isTwoComponentIn hJtc
  have hJK : J ≤ FooteLit.solomonKStarOf C := by
    have h := h212 X J T hJs hTne hT2 hTJ
    rwa [hCT, hJinf, hJlayer] at h
  have hKL : FooteLit.solomonKStarOf C ≤ FooteLit.twoLayerIn C :=
    iSup₂_le fun K hK => FooteLit.le_twoLayerIn_of_isTwoComponentIn hK.1
  have hJL : J ≤ FooteLit.twoLayerIn C := hJK.trans hKL
  have hpump : ∀ K, FooteLit.IsTwoComponentIn K C → ¬ J ≤ coreActionKernel K →
      FooteLit.SolomonEquiv J K := by
    intro K hK hJK'
    have hKP := Sol76.isTwoComponentIn_conjClosure_of_not_le hK hJL hJK'
    have hlt : FooteLit.SolomonLt J K := by
      refine ⟨hJmem, Sol76.isSolomonMember_of_isTwoComponentIn_centralizer hy hK, T, hT2, hTJ,
        ?_⟩
      rwa [hCT, hJinf, hJlayer]
    exact hJs.1.2 J K ⟨hJmem, Relation.ReflTransGen.refl⟩ hlt
  obtain ⟨eJ⟩ := nonempty_fusionZStar_equiv_of_coreQuotient (by omega) e
  have hrank3 : ∀ K, FooteLit.SolomonEquiv J K → 3 ≤ CFSG.pRank 2 K := fun K h =>
    Sol76.three_le_pRank_of_solomonEquiv hS h (by omega) eJ
  have hrJ : 3 ≤ CFSG.pRank 2 J := three_le_pRank_of_coreQuotient (by omega) e
  set S : Set (Subgroup X) := {K | FooteLit.IsTwoComponentIn K C ∧ K ∈ FooteLit.solomonKStar X}
    with hSdef
  have hSfin : S.Finite := Set.toFinite S
  set s := hSfin.toFinset with hs
  have hs1 : s.card ≤ 1 := by
    by_contra hcard
    rw [not_le] at hcard
    set ee := s.equivFin.symm with hee
    set Kf : Fin s.card → Subgroup X := fun i => ((ee i : s) : Subgroup X) with hKf
    have hKfS : ∀ i, Kf i ∈ S := fun i => hSfin.mem_toFinset.mp (ee i).2
    have hbal : FooteLit.IsKBalanced C := by
      refine ⟨s.card, Kf, fun i j hij => ee.injective (Subtype.ext hij), fun K => ⟨fun hK => ?_,
        ?_⟩, hcard, fun i j hij => ?_, ?_, ?_⟩
      · refine ⟨ee.symm ⟨K, hSfin.mem_toFinset.mpr hK⟩, ?_⟩
        simp only [hKf, Equiv.apply_symm_apply]
      · rintro ⟨i, rfl⟩
        exact hKfS i
      · exact FooteLit.commutator_le_oddCoreIn_of_ne (hKfS i).1 (hKfS j).1
          (fun h => hij (ee.injective (Subtype.ext h)))
      ·
        by_cases hex : ∃ i, J ≤ coreActionKernel (Kf i)
        · obtain ⟨i, hi⟩ := hex
          exact ⟨i, hrJ.trans (pRank_le_of_le (le_inf (hJL.trans le_sup_right) hi))⟩
        · push Not at hex
          set i₀ : Fin s.card := ⟨0, by omega⟩ with hi₀
          set i₁ : Fin s.card := ⟨1, hcard⟩ with hi₁
          have hne : Kf i₀ ≠ Kf i₁ := by
            intro h
            have h' := ee.injective (Subtype.ext h)
            rw [hi₀, hi₁, Fin.mk.injEq] at h'
            omega
          refine ⟨i₀, (hrank3 _ (hpump _ (hKfS i₁).1 (hex i₁))).trans (pRank_le_of_le ?_)⟩
          exact le_inf ((FooteLit.le_twoLayerIn_of_isTwoComponentIn (hKfS i₁).1).trans
            le_sup_right) (GSThmB.B5a.le_coreActionKernel_of_ne (hKfS i₀).1.1 (hKfS i₁).1.1
              (hKfS i₀).1.2 (hKfS i₁).1.2 hne)
      ·
        right; left
        have hyC : y ∈ C := mem_centralizer_singleton_iff.mpr rfl
        have hyO : y ∈ FooteLit.oddTwoCoreIn C := FooteLit.mem_oddTwoCoreIn_of_central hyC
          (fun c hc => mem_centralizer_singleton_iff.mp hc) hy
        have hKC : FooteLit.solomonKStarOf C ≤ C := iSup₂_le fun K hK => hK.1.1
        have hyY : y ∈ (FooteLit.oddTwoCoreIn C ⊔ FooteLit.twoLayerIn C) ⊓
            coreActionKernel (FooteLit.solomonKStarOf C) :=
          mem_inf.mpr ⟨mem_sup_left hyO, mem_coreActionKernel_of_commute fun c hc =>
            mem_centralizer_singleton_iff.mp (hKC hc)⟩
        exact FooteLit.one_le_pRank_of_orderOf_eq_two (g := ⟨y, hyY⟩)
          (by rw [Subgroup.orderOf_mk]; exact hy)
    exact (h13 X inferInstance hna hK C hbal).elim
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hbot : FooteLit.solomonKStarOf C = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun K hK => ?_)
      have hKs : K ∈ s := hSfin.mem_toFinset.mpr hK
      rw [hemp] at hKs
      exact absurd hKs (Finset.notMem_empty K)
    exact hJne (le_bot_iff.mp (hbot ▸ hJK))
  obtain ⟨K₁, hK₁s⟩ := hsne
  have hK₁S : K₁ ∈ S := hSfin.mem_toFinset.mp hK₁s
  have huniq : ∀ K ∈ S, K = K₁ := fun K hK =>
    Finset.card_le_one.mp hs1 K (hSfin.mem_toFinset.mpr hK) K₁ hK₁s
  have hKstar : FooteLit.solomonKStarOf C = K₁ :=
    le_antisymm (iSup₂_le fun K hK => (huniq K hK).le) (le_iSup₂_of_le K₁ hK₁S le_rfl)
  have hJK₁ : J ≤ K₁ := hKstar ▸ hJK
  have hnot : ¬ J ≤ coreActionKernel K₁ := by
    intro h
    have hJO : J ≤ FooteLit.oddCoreIn K₁ := by
      rw [← hperf]
      refine commutator_le.mpr fun a ha b hb => ?_
      have h1 := (h (inv_mem hb)).2 a⁻¹ (hJK₁ (inv_mem ha))
      rwa [inv_inv, inv_inv, ← commutatorElement_def] at h1
    have hrJ' := hrJ
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at hrJ'
    obtain ⟨b, hbJ, hb2⟩ := Sol76.exists_orderOf_eq_two_of_pRank (K := J) (by omega)
    have h1 := orderOf_dvd_natCard (⟨b, hJO hbJ⟩ : FooteLit.oddCoreIn K₁)
    rw [Subgroup.orderOf_mk, hb2] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd (Sol76.coprime_card_oddCoreIn K₁) h1) (by norm_num)
  have hequiv : FooteLit.SolomonEquiv J K₁ := hpump K₁ hK₁S.1 hnot
  obtain ⟨eK⟩ : Nonempty (K₁ ⧸ Open.fusionZStar K₁ ≃* alternatingGroup (Fin n)) := by
    obtain ⟨e'⟩ := Sol76.nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
    exact ⟨e'.symm.trans eJ⟩
  have hK₁perf : ⁅K₁, K₁⁆ = K₁ := (Sol76.isSolomonMember_of_reflTransGen hequiv.1 hequiv.2).1
  have hZ : Nat.card (center (↥K₁ ⧸ pPrimeCore 2 ↥K₁)) ≤ 2 := by
    have : Group.IsPerfect K₁ := Subgroup.isPerfect_iff.mpr hK₁perf
    exact card_center_le_two hS (pPrimeCore_quotient_pPrimeCore_eq_bot 2) (by omega)
      ((coreQuotientCenterEquiv K₁).trans eK)
  have hJO : J ⊔ FooteLit.oddCoreIn K₁ = K₁ := Sol76.sup_oddCoreIn_eq_of_le hJK₁ hK₁perf eK hZ e
  have hK₁n : C ≤ normalizer (K₁ : Set X) := by
    intro h hh
    have hconj : conjugate K₁ h⁻¹ ∈ S :=
      ⟨Sol76.isTwoComponentIn_map_conj hK₁S.1 (le_normalizer (inv_mem (inv_mem hh))),
        Sol76.conjugate_mem_solomonKStar hK₁S.2 h⁻¹⟩
    have h1 := huniq _ hconj
    rw [conjugate, inv_inv] at h1
    exact mem_normalizer_iff_map_conj_eq.mpr h1
  set W := FooteLit.oddCoreIn C ⊔ J with hW
  have hO₁ : FooteLit.oddCoreIn K₁ ≤ FooteLit.oddCoreIn C :=
    FooteLit.oddCoreIn_le_of_isTwoComponentIn hK₁S.1
  have key : ∀ h ∈ C, ∀ x ∈ W, h * x * h⁻¹ ∈ W := by
    intro h hh x hx
    have hmap : W.map (MulAut.conj h).toMonoidHom ≤ W := by
      rw [hW, Subgroup.map_sup,
        Sol76.map_conj_oddCoreIn (le_normalizer hh : h ∈ normalizer (C : Set X))]
      refine sup_le le_sup_left ?_
      calc J.map (MulAut.conj h).toMonoidHom ≤ K₁.map (MulAut.conj h).toMonoidHom :=
            map_mono hJK₁
        _ = K₁ := Sol76.map_conj_eq_of_mem_normalizer (hK₁n hh)
        _ = J ⊔ FooteLit.oddCoreIn K₁ := hJO.symm
        _ ≤ W := sup_le le_sup_right (hO₁.trans le_sup_left)
    have := hmap (mem_map_of_mem _ hx)
    simpa [MulAut.conj_apply] using this
  intro h hh
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key h hh x
  · intro hx
    have := key h⁻¹ (inv_mem hh) _ hx
    simpa [mul_assoc] using this

theorem maximalAltComponent_of_thm13 (h13 : Sol76T13.SolomonThm13Simple)
    (h212 : Sol76.Lemma212Input) (hmax : MaximalityLemmaInput)
    (hS : SolAltLit.SchurAlternatingMultiplierInput) : SolAltLit.MaximalAltComponentInput := by
  intro X _ _ _ hna hK hz hU t J n hJ hn hn9 hmaxdeg
  have hJs := mem_solomonKStar_of_isAltTwoComponent hmax hS hna hK hz hU hJ hn hn9 hmaxdeg
  exact ⟨fun g => commutator_conjugate_ne_bot h13 hna hK hJ hn9 hJs g,
    fun y hy hJy => le_normalizer_oddCoreIn_sup h13 h212 hS hna hK hJ hn9 hJs hy hJy⟩

end CFSG.ComponentClassification.Sol78
