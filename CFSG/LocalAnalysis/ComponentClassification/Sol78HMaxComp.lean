module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78HAltPair
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Proof

public section

namespace CFSG.ComponentClassification.Sol78H

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem exists_central_involution [Finite X] {S : Subgroup X} (hS1 : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) : ∃ z ∈ S, orderOf z = 2 ∧ ∀ s ∈ S, s * z = z * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥S := (nontrivial_iff_ne_bot S).mpr hS1
  have hZ := hS2.center_nontrivial
  have := Fintype.ofFinite ↥(center ↥S)
  have h2 : 2 ∣ Fintype.card ↥(center ↥S) := by
    have hZ2 : IsPGroup 2 ↥(center ↥S) := hS2.to_subgroup _
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have := Finite.one_lt_card_iff_nontrivial.mpr hZ
      omega
    rw [← Nat.card_eq_fintype_card, hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card 2 h2
  refine ⟨((z₀ : ↥S) : X), (z₀ : ↥S).2, ?_, fun s hs => ?_⟩
  · rw [orderOf_coe, orderOf_coe, hz₀]
  · have h1 := (mem_center_iff.mp z₀.2) ⟨s, hs⟩
    exact congrArg Subtype.val h1

variable [Finite X]

theorem le_normalizer_oddCoreIn_sup_of_two_group (h13 : Sol76T13.SolomonThm13Simple)
    (hS : SolAltLit.SchurAlternatingMultiplierInput) [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    {Y₀ J : Subgroup X} {n : ℕ} (hJtc : FooteLit.IsTwoComponentIn J Y₀) (hn9 : 9 ≤ n)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (hJs : J ∈ FooteLit.solomonKStar X)
    {S Y : Subgroup X} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hJS : J ≤ centralizer (S : Set X)) (hCY : centralizer (S : Set X) ≤ Y)
    (hYN : Y ≤ normalizer (S : Set X)) :
    Y ≤ normalizer ((FooteLit.oddCoreIn Y ⊔ J : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (S : Set X) with hC
  have hJmem : FooteLit.IsSolomonMember J := hJs.1.1
  have hperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJtc.1 hJtc.2
  have hJne : J ≠ ⊥ := fun h =>
    Sol78.ne_bot_of_isPComponent' hJtc.2 (by rw [h]; exact bot_subgroupOf _)
  have hTJ : S ≤ coreActionKernel J := fun s hs =>
    Sol78.mem_coreActionKernel_of_commute fun j hj => ((mem_centralizer_iff.mp (hJS hj)) s hs).symm
  have hJinf : J ⊓ C = J := inf_eq_left.mpr hJS
  have hJlayer : FooteLit.twoLayerIn J = J := Sol76.twoLayerIn_eq_self_of_isTwoComponentIn hJtc
  have hJK : J ≤ FooteLit.solomonKStarOf C := by
    have h := Sol76.lemma212Input X J S hJs hS1 hS2 hTJ
    rwa [hJinf, hJlayer] at h
  have hKL : FooteLit.solomonKStarOf C ≤ FooteLit.twoLayerIn C :=
    iSup₂_le fun K hK => FooteLit.le_twoLayerIn_of_isTwoComponentIn hK.1
  have hJL : J ≤ FooteLit.twoLayerIn C := hJK.trans hKL
  have hpump : ∀ K, FooteLit.IsTwoComponentIn K C → ¬ J ≤ coreActionKernel K →
      FooteLit.SolomonEquiv J K := by
    intro K hK hJK'
    have hKP := Sol76.isTwoComponentIn_conjClosure_of_not_le hK hJL hJK'
    have hlt : FooteLit.SolomonLt J K := by
      refine ⟨hJmem, Sol76.isSolomonMember_of_isTwoComponentIn hS1 hS2 hK, S, hS2, hTJ, ?_⟩
      rwa [hJinf, hJlayer]
    exact hJs.1.2 J K ⟨hJmem, Relation.ReflTransGen.refl⟩ hlt
  obtain ⟨eJ⟩ := Sol78.nonempty_fusionZStar_equiv_of_coreQuotient (by omega) e
  have hrank3 : ∀ K, FooteLit.SolomonEquiv J K → 3 ≤ CFSG.pRank 2 K := fun K h =>
    Sol76.three_le_pRank_of_solomonEquiv hS h (by omega) eJ
  have hrJ : 3 ≤ CFSG.pRank 2 J := Sol78.three_le_pRank_of_coreQuotient (by omega) e
  obtain ⟨z, hzS, hz2, hzc⟩ := exists_central_involution hS1 hS2
  have hzC : z ∈ C := mem_centralizer_iff.mpr fun s hs => hzc s hs
  have hzcent : ∀ c ∈ C, c * z = z * c := fun c hc =>
    ((mem_centralizer_iff.mp hc) z hzS).symm
  set Sset : Set (Subgroup X) :=
    {K | FooteLit.IsTwoComponentIn K C ∧ K ∈ FooteLit.solomonKStar X} with hSdef
  have hSfin : Sset.Finite := Set.toFinite Sset
  set s := hSfin.toFinset with hs
  have hs1 : s.card ≤ 1 := by
    by_contra hcard
    rw [not_le] at hcard
    set ee := s.equivFin.symm with hee
    set Kf : Fin s.card → Subgroup X := fun i => ((ee i : s) : Subgroup X) with hKf
    have hKfS : ∀ i, Kf i ∈ Sset := fun i => hSfin.mem_toFinset.mp (ee i).2
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
          exact ⟨i, hrJ.trans (Sol78.pRank_le_of_le (le_inf (hJL.trans le_sup_right) hi))⟩
        · push Not at hex
          set i₀ : Fin s.card := ⟨0, by omega⟩ with hi₀
          set i₁ : Fin s.card := ⟨1, hcard⟩ with hi₁
          have hne : Kf i₀ ≠ Kf i₁ := by
            intro h
            have h' := ee.injective (Subtype.ext h)
            rw [hi₀, hi₁, Fin.mk.injEq] at h'
            omega
          refine ⟨i₀, (hrank3 _ (hpump _ (hKfS i₁).1 (hex i₁))).trans (Sol78.pRank_le_of_le ?_)⟩
          exact le_inf ((FooteLit.le_twoLayerIn_of_isTwoComponentIn (hKfS i₁).1).trans
            le_sup_right) (GSThmB.B5a.le_coreActionKernel_of_ne (hKfS i₀).1.1 (hKfS i₁).1.1
              (hKfS i₀).1.2 (hKfS i₁).1.2 hne)
      ·
        right; left
        have hzO : z ∈ FooteLit.oddTwoCoreIn C :=
          FooteLit.mem_oddTwoCoreIn_of_central hzC hzcent hz2
        have hKC : FooteLit.solomonKStarOf C ≤ C := iSup₂_le fun K hK => hK.1.1
        have hzY : z ∈ (FooteLit.oddTwoCoreIn C ⊔ FooteLit.twoLayerIn C) ⊓
            coreActionKernel (FooteLit.solomonKStarOf C) :=
          mem_inf.mpr ⟨mem_sup_left hzO, Sol78.mem_coreActionKernel_of_commute fun c hc =>
            hzcent c (hKC hc)⟩
        exact FooteLit.one_le_pRank_of_orderOf_eq_two (g := ⟨z, hzY⟩)
          (by rw [Subgroup.orderOf_mk]; exact hz2)
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
  have hK₁S : K₁ ∈ Sset := hSfin.mem_toFinset.mp hK₁s
  have huniq : ∀ K ∈ Sset, K = K₁ := fun K hK =>
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
    exact Sol78.card_center_le_two hS (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) (by omega)
      ((Sol78.coreQuotientCenterEquiv K₁).trans eK)
  have hJO : J ⊔ FooteLit.oddCoreIn K₁ = K₁ := Sol76.sup_oddCoreIn_eq_of_le hJK₁ hK₁perf eK hZ e
  have hK₁n : Y ≤ normalizer (K₁ : Set X) := by
    intro h hh
    have hhC : h⁻¹⁻¹ ∈ normalizer (C : Set X) :=
      mem_normalizer_centralizer (hYN (inv_mem (inv_mem hh)))
    have hconj : conjugate K₁ h⁻¹ ∈ Sset :=
      ⟨Sol76.isTwoComponentIn_map_conj hK₁S.1 hhC, Sol76.conjugate_mem_solomonKStar hK₁S.2 h⁻¹⟩
    have h1 := huniq _ hconj
    rw [conjugate, inv_inv] at h1
    exact mem_normalizer_iff_map_conj_eq.mpr h1
  have hK₁Y : FooteLit.IsTwoComponentIn K₁ Y :=
    Sol78.isTwoComponentIn_of_le_normalizer hK₁S.1 (hK₁S.1.1.trans hCY) hK₁n
  have hO₁ : FooteLit.oddCoreIn K₁ ≤ FooteLit.oddCoreIn Y :=
    FooteLit.oddCoreIn_le_of_isTwoComponentIn hK₁Y
  set W := FooteLit.oddCoreIn Y ⊔ J with hW
  have key : ∀ h ∈ Y, ∀ x ∈ W, h * x * h⁻¹ ∈ W := by
    intro h hh x hx
    have hmap : W.map (MulAut.conj h).toMonoidHom ≤ W := by
      rw [hW, Subgroup.map_sup,
        Sol76.map_conj_oddCoreIn (le_normalizer hh : h ∈ normalizer (Y : Set X))]
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

theorem le_normalizer_core_sup_of_thm13 (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {n : ℕ} (hn : Odd n) (hn9 : 9 ≤ n)
    (hex : ∃ (t : X) (J : Subgroup X), SolAltLit.IsAltTwoComponent t J n)
    (hmaxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n) {T K : Subgroup X} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hKT : FooteLit.IsTwoComponentIn K (centralizer (T : Set X)))
    (eK : Nonempty (K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin n))) {S Y : Subgroup X}
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hKS : K ≤ centralizer (S : Set X))
    (hCY : centralizer (S : Set X) ≤ Y) (hYN : Y ≤ normalizer (S : Set X)) :
    Y ≤ normalizer ((GH74.GLS.pPrimeCoreOf 2 Y ⊔ K : Subgroup X) : Set X) := by
  obtain ⟨e⟩ := eK
  have hKs := mem_solomonKStar_of_member hmax hS hna hK hz hU hn hn9 hex hmaxdeg
    (Sol76.isSolomonMember_of_isTwoComponentIn hT hT2 hKT) e
  exact le_normalizer_oddCoreIn_sup_of_two_group h13 hS hna hK hKT hn9 e hKs hS1 hS2 hKS hCY hYN

theorem le_normalizer_core_sup_of_thm13_centralizer (h13 : Sol76T13.SolomonThm13Simple)
    (hmax : Sol78.MaximalityLemmaInput) (hS : SolAltLit.SchurAlternatingMultiplierInput)
    [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {n : ℕ} (hn : Odd n) (hn9 : 9 ≤ n)
    (hex : ∃ (t : X) (J : Subgroup X), SolAltLit.IsAltTwoComponent t J n)
    (hmaxdeg : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n) {T K : Subgroup X} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hKT : FooteLit.IsTwoComponentIn K (centralizer (T : Set X)))
    (eK : Nonempty (K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin n))) {u : X}
    (hu : orderOf u = 2) (hKu : K ≤ centralizer ({u} : Set X)) :
    centralizer ({u} : Set X) ≤ normalizer
      ((GH74.GLS.pPrimeCoreOf 2 (centralizer ({u} : Set X)) ⊔ K : Subgroup X) : Set X) := by
  have hCU : centralizer ((zpowers u : Subgroup X) : Set X) = centralizer ({u} : Set X) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hU1 : zpowers u ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hu
    norm_num at hu
  have hU2 : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  have hKU : K ≤ centralizer ((zpowers u : Subgroup X) : Set X) := by
    rw [hCU]
    exact hKu
  refine le_normalizer_core_sup_of_thm13 h13 hmax hS hna hK hz hU hn hn9 hex hmaxdeg hT hT2 hKT
    eK hU1 hU2 hKU hCU.le fun c hc => ?_
  have hc' : c ∈ centralizer ((zpowers u : Subgroup X) : Set X) := by
    rw [hCU]
    exact hc
  exact Subgroup.centralizer_le_normalizer _ hc'

end CFSG.ComponentClassification.Sol78H
