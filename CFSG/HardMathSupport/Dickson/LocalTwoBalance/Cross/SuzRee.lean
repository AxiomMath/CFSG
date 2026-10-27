module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6CrossRed
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzMain
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section ReeG2Five


theorem localTwoCrossFamCat_five_reeG2 : LocalTwoCrossFamCat 5 .reeG2 := by
  rintro ⟨d, hv⟩ ⟨m, rfl⟩ _ _
  have hp : Nat.Prime 5 := by norm_num
  have hp3 : 3 < 5 := by norm_num
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat_G2 hv
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_two_reeGamma_G2 hm1 hX hp hp3)

end ReeG2Five

section Suzuki

variable {a : ℕ} {F : Type} [Field F] [Finite F]

private theorem suzuki_prime_faithful_odd (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hne : a = 2 → p ≠ 5) {σ : RingAut F}
    (hσ : orderOf σ = p) {b : ℕ} {k : Type} [Field k] [Finite k]
    (hbp : (2 * b + 1) * p = 2 * a + 1) (hkc : Nat.card k = 2 ^ (2 * b + 1))
    (eH : ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) ≃* suzukiGroup b k)
    (hdvd : p ∣ Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)))
    (g : MulAut (suzukiGroup a F)) (hgr : (orderOf g).Prime) (hgp : orderOf g ≠ p)
    (hcomm : g * szFieldAut a F σ = szFieldAut a F σ * g)
    (hfix : ∀ u ∈ (szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _), g u = u) : False := by
  have hinj : Function.Injective (MulAut.conj : suzukiGroup a F →* MulAut (suzukiGroup a F)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hF)
  have hp2 : p ≠ 2 := by omega
  set δ := szFieldAut a F σ with hδ
  by_cases hin : ∃ c : suzukiGroup a F, MulAut.conj c = g
  · obtain ⟨c, hc⟩ := hin
    have h1 : δ * MulAut.conj c = MulAut.conj c * δ := by rw [hc]; exact hcomm.symm
    have hcδ : δ c = c := mem_fixSub_of_commute hinj h1
    have hcz : c = 1 := by
      refine CFSG.RankThree.PartOne.SEITZ2.eq_one_of_central_fixed_szFieldAut hp hp5 hF
        hne hσ ?_ (x := c) ?_ ?_
      · rw [CFSG.RankThree.PartOne.SEITZ2.fixedSubgroup_eq_eqLocus]
        exact hdvd
      · rw [CFSG.RankThree.PartOne.SEITZ2.fixedSubgroup_eq_eqLocus]
        exact hcδ
      · intro y hy
        rw [CFSG.RankThree.PartOne.SEITZ2.fixedSubgroup_eq_eqLocus] at hy
        have := hfix y hy
        rw [← hc] at this
        simp only [MulAut.conj_apply] at this
        calc c * y = (c * y * c⁻¹) * c := by group
          _ = y * c := by rw [this]
    rw [hcz, map_one] at hc
    rw [← hc] at hgr
    simp at hgr
    exact Nat.not_prime_one hgr
  ·
    set r := orderOf g with hr
    have hgord : orderOf g = r := rfl
    have hr2 : r ≠ 2 := by
      intro h2
      have hg2 : g ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one g
      have hout := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hF).2
      have hbar1 : (QuotientGroup.mk g : Outer (suzukiGroup a F)) ≠ 1 := by
        intro h
        rw [QuotientGroup.eq_one_iff] at h
        exact hin h
      have hbar2 : (QuotientGroup.mk g : Outer (suzukiGroup a F)) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow, hg2]; rfl
      have hord2 : orderOf (QuotientGroup.mk g : Outer (suzukiGroup a F)) = 2 :=
        orderOf_eq_prime hbar2 hbar1
      have : 2 ∣ Nat.card (Outer (suzukiGroup a F)) := hord2 ▸ orderOf_dvd_natCard _
      have := this.trans hout
      omega
    obtain ⟨σ', h', c', k', _, _, hσ', hcr, hkc', hconj', ⟨eH'⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hF r hgr hr2 g hgord
        (fun ⟨y, hy⟩ => hin ⟨y, hy⟩)
    set m := 2 * b + 1 with hm
    set s := 2 * c' + 1 with hs
    have hJ1 : Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) =
        (2 ^ m) ^ 2 * (2 ^ m - 1) * ((2 ^ m) ^ 2 + 1) := by
      rw [Nat.card_congr eH.toEquiv]
      exact CFSG.LieType.Ree.suzuki_order hkc
    have hJle : (szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _) ≤ fixSub g :=
      fun u hu => hfix u hu
    have hdvd1 := Subgroup.card_dvd_of_le hJle
    have hfs : fixSub (szFieldAut a F σ') =
        (szFieldAut a F σ').toMonoidHom.eqLocus (MonoidHom.id _) := by
      ext z; rfl
    have hC : Nat.card (fixSub g) = (2 ^ s) ^ 2 * (2 ^ s - 1) * ((2 ^ s) ^ 2 + 1) := by
      rw [← card_fixSub_conj (MulAut.conj h') g, hconj', hfs, Nat.card_congr eH'.toEquiv]
      exact CFSG.LieType.Ree.suzuki_order hkc'
    rw [hJ1, hC] at hdvd1
    have hA : 2 ^ m - 1 ∣ (2 ^ s) ^ 2 * (2 ^ s - 1) * ((2 ^ s) ^ 2 + 1) :=
      (dvd_mul_of_dvd_left (dvd_mul_left (2 ^ m - 1) _) _).trans hdvd1
    have hnd : ¬ m ∣ s := by
      rintro ⟨t, ht⟩
      have h1 : m * p = m * (t * r) := by
        calc m * p = 2 * a + 1 := hbp
          _ = s * r := hcr.symm
          _ = m * (t * r) := by rw [ht, mul_assoc]
      have hm0 : 0 < m := by omega
      have h2 : p = t * r := Nat.eq_of_mul_eq_mul_left hm0 h1
      have h3 : r ∣ p := ⟨t, by rw [h2, mul_comm]⟩
      exact hgp ((Nat.prime_dvd_prime_iff_eq hgr hp).1 h3)
    refine not_dvd_suzuki_order (m := m) (s := s) ⟨b, rfl⟩ hnd ?_
    have : (2 ^ s) ^ 2 * (2 ^ s - 1) * ((2 ^ s) ^ 2 + 1) =
        (2 ^ s) ^ 2 * ((2 ^ s) ^ 2 + 1) * (2 ^ s - 1) := by ring
    rwa [this] at hA

end Suzuki

theorem isLocallyBalancedAbs_two_suzukiGroup_odd
    {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hne : a = 2 → p ≠ 5) : IsLocallyBalancedAbs p 2 (suzukiGroup a F) := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (MulAut.conj : suzukiGroup a F →* MulAut (suzukiGroup a F)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hF)
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj ?_ ?_
  · intro E hEin hE hEc H hH
    exact (suzuki_no_inner_plane ha hF hp hp2 hE hEc hEin).elim
  · intro D hD hDc hDin
    have hDe := CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian hD
    obtain ⟨g, hg1, hgD⟩ := CFSG.RankThree.PartOne.SEITZ2.exists_conj_mem_of_plane_suzuki hp ha hF D
      hDc
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    have hxp : x ^ p = 1 := hD.2 x hxD
    have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
    obtain ⟨σ, h, b, k, _, _, hσp, hbp, hkc, hconj, ⟨eH⟩⟩ :=
      CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hF p hp hp2 x hxord
        (fun ⟨y, hy⟩ => hxin ⟨y, hy⟩)
    set δ := szFieldAut a F σ with hδ
    have hδp : orderOf δ = p := by
      rw [hδ, orderOf_injective (szFieldAut a F) szFieldAut_injective, hσp]
    have hxh : x = (MulAut.conj h)⁻¹ * δ * (MulAut.conj h)⁻¹⁻¹ := by
      rw [← hconj]; group
    have hy1 : (MulAut.conj g : MulAut (suzukiGroup a F)) ≠ 1 := fun h1 =>
      hg1 (hinj (by rw [h1, map_one]))
    have hyp : (MulAut.conj g : MulAut (suzukiGroup a F)) ^ p = 1 := hD.2 _ hgD
    have hcomm : (MulAut.conj g : MulAut (suzukiGroup a F)) * x = x * MulAut.conj g :=
      congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hgD⟩ ⟨x, hxD⟩)
    obtain ⟨k₀, hk₀δ, hk₀ord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh ⟨g, rfl⟩ hy1
      hyp hcomm
    have hJdvd : p ∣ Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) := by
      have hk₀J : k₀ ∈ (szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _) := hk₀δ
      have : orderOf (⟨k₀, hk₀J⟩ : ↥((szFieldAut a F σ).toMonoidHom.eqLocus
          (MonoidHom.id _))) = p := by
        rw [Subgroup.orderOf_mk]
        exact hk₀ord
      rw [← this]
      exact orderOf_dvd_natCard _
    have hb1 : 1 ≤ b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      subst hb0'
      have h20 : Nat.card ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) = 20 := by
        rw [Nat.card_congr eH.toEquiv, CFSG.LieType.Ree.suzuki_order hkc]
        norm_num
      rw [h20] at hJdvd
      have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) hJdvd
      interval_cases p <;> omega
    obtain ⟨-, hnt, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple hb1 hkc
    have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot hb1 hkc
    have : IsSimpleGroup ↥((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) :=
      eH.isSimpleGroup
    have hJq : CFSG.IsQuasisimple ((szFieldAut a F σ).toMonoidHom.eqLocus (MonoidHom.id _)) :=
      isQuasisimple_of_simple_nonabelian fun hc => by
        have hcen : Subgroup.center (suzukiGroup b k) = ⊤ :=
          Subgroup.eq_top_iff' _ |>.2 fun z => Subgroup.mem_center_iff.2 fun w => by
            have := congrArg eH (hc (eH.symm w) (eH.symm z))
            rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
            exact this
        obtain ⟨z, hz⟩ := exists_ne (1 : suzukiGroup b k)
        have hz' : z ∈ Subgroup.center (suzukiGroup b k) := by rw [hcen]; trivial
        rw [hZ] at hz'
        exact hz (Subgroup.mem_bot.1 hz')
    refine ⟨x, hxD, hxin, ?_⟩
    refine fieldCoreAt_of_canonical_conj_primeFaithful hp hinj hδp hJq (fun z => Iff.rfl) ?_ hxh
      ⟨g, rfl⟩ hy1 hyp hcomm
    intro g' hgr hgp hc' hfix
    exact suzuki_prime_faithful_odd ha hF hp hp5 hne hσp hbp hkc eH hJdvd g' hgr hgp hc' hfix

section ThirtyTwo

variable {G J' : Type*} [Group G] [Group J']

private theorem eq_bot_of_normal_of_equiv_five {J : Subgroup G} (e : J ≃* J')
    (hJ' : ∀ R : Subgroup J', R.Normal → Nat.Coprime (Nat.card R) 5 → R = ⊥)
    {N : Subgroup G} (hNJ : N ≤ J) (hNn : ∀ f ∈ J, ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hcop : Nat.Coprime 5 (Nat.card N)) : N = ⊥ := by
  have hnorm : (N.subgroupOf J).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn g.1 g.2 n.1 hn⟩
  have hR : ((N.subgroupOf J).map e.toMonoidHom).Normal := hnorm.map _ e.surjective
  have hcard : Nat.card ((N.subgroupOf J).map e.toMonoidHom) = Nat.card N := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNJ).toEquiv
  have h1 := hJ' _ hR (by rw [hcard]; exact hcop.symm)
  have h2 : Nat.card N = 1 := by
    rw [← hcard, h1, Subgroup.card_bot]
  exact Subgroup.eq_bot_of_card_eq _ h2

end ThirtyTwo

private theorem coreFreeAt_five_suzuki_outer {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2 ^ 5) {x : MulAut (suzukiGroup 2 F)} (hxord : orderOf x = 5)
    (hxin : x ∉ innerAut (suzukiGroup 2 F)) : CoreFreeAt 5 x := by
  have ha : 1 ≤ 2 := by norm_num
  have hF' : Nat.card F = 2 ^ (2 * 2 + 1) := by rw [hF]
  have hinj : Function.Injective
      (MulAut.conj : suzukiGroup 2 F →* MulAut (suzukiGroup 2 F)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hF')
  obtain ⟨σ, h, b, k, _, _, hσp, hbp, hkc, hconj, ⟨eH⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent 2 ha F hF' 5 (by norm_num)
      (by norm_num) x hxord (fun ⟨y, hy⟩ => hxin ⟨y, hy⟩)
  have hb0 : b = 0 := by omega
  subst hb0
  have hk2 : Nat.card k = 2 := by simpa using hkc
  have hcore := (CFSG.LieType.Ree.suzuki_two_normal_five_complement_core_trivial hk2).2
  obtain ⟨_, -, -, -, hRbot⟩ := hcore
  set δ := szFieldAut 2 F σ with hδ
  have hfs : fixSub δ = (szFieldAut 2 F σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext z; rfl
  have hA : ∀ N : Subgroup (suzukiGroup 2 F), N ≤ fixSub δ →
      (∀ f ∈ fixSub δ, ∀ n ∈ N, f * n * f⁻¹ ∈ N) → Nat.Coprime 5 (Nat.card N) → N = ⊥ := by
    intro N hNJ hNn hcop
    rw [hfs] at hNJ hNn
    exact eq_bot_of_normal_of_equiv_five eH hRbot hNJ hNn hcop
  have hcf : CoreFreeAt 5 δ := by
    refine ⟨hA, fun g hg hgδ hfix => ?_⟩
    have hout := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hF').2
    have hord : orderOf (QuotientGroup.mk g : Outer (suzukiGroup 2 F)) ∣ 5 := by
      refine (orderOf_dvd_natCard _).trans ?_
      simpa using hout
    have hord' : orderOf (QuotientGroup.mk g : Outer (suzukiGroup 2 F)) ∣ orderOf g :=
      orderOf_map_dvd (QuotientGroup.mk' (inner (suzukiGroup 2 F))) g
    have hord1 : orderOf (QuotientGroup.mk g : Outer (suzukiGroup 2 F)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hg hord hord'
    have hgin : g ∈ inner (suzukiGroup 2 F) := by
      rw [← QuotientGroup.eq_one_iff]
      exact orderOf_eq_one_iff.1 hord1
    obtain ⟨c, hc⟩ := hgin
    have h1 : δ * MulAut.conj c = MulAut.conj c * δ := by rw [hc]; exact hgδ.symm
    have hcδ : c ∈ fixSub δ := mem_fixSub_of_commute hinj h1
    have hcomm : ∀ t ∈ fixSub δ, c * t = t * c := by
      intro t ht
      have := hfix t ht
      rw [← hc] at this
      simp only [MulAut.conj_apply] at this
      calc c * t = (c * t * c⁻¹) * c := by group
        _ = t * c := by rw [this]
    have hz : Subgroup.zpowers c = ⊥ := by
      refine hA _ (Subgroup.zpowers_le.2 hcδ) (fun f hf n hn => ?_) ?_
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
        have hfc : Commute f c := (hcomm f hf).symm
        rw [(hfc.zpow_right m).eq]
        simpa using Subgroup.zpow_mem_zpowers c m
      · rw [Nat.card_zpowers, ← orderOf_injective _ hinj c, hc]
        exact hg
    have hc1 : c = 1 := Subgroup.zpowers_eq_bot.1 hz
    rw [← hc, hc1, map_one]
  have hxh : x = (MulAut.conj h)⁻¹ * δ * (MulAut.conj h)⁻¹⁻¹ := by
    rw [← hconj]; group
  rw [hxh]
  exact hcf.conj _

theorem isLocallyBalancedAbs_two_suzukiGroup_thirtyTwo
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 5) :
    IsLocallyBalancedAbs 5 2 (suzukiGroup 2 F) := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have ha : 1 ≤ 2 := by norm_num
  have hF' : Nat.card F = 2 ^ (2 * 2 + 1) := by rw [hF]
  have hinj : Function.Injective
      (MulAut.conj : suzukiGroup 2 F →* MulAut (suzukiGroup 2 F)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hF')
  intro D hD hDc H hH _
  by_cases hDin : D ≤ innerAut (suzukiGroup 2 F)
  · exact (suzuki_no_inner_plane ha hF' hp (by norm_num) hD hDc hDin).elim
  · obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    have hxp : x ^ 5 = 1 := hD.2 x hxD
    have hxord : orderOf x = 5 := orderOf_eq_prime hxp hx1
    exact localDeltaIn_eq_bot_of_coreFree hp hinj hH hxD hx1
      (coreFreeAt_five_suzuki_outer hF hxord hxin)

theorem localTwoCrossFamCat_three_suzuki :
    LocalTwoCrossFamCat 3 .suzuki := by
  rintro ⟨d, hv⟩ ⟨m, hd⟩ _ _ D hD hcard H hH hDH
  change d = _ at hd
  subst hd
  exact (CFSG.LieType.SeitzGeneration.no_plane_suzuki_three hv hD hcard).elim

theorem localTwoCrossFamCat_five_suzuki :
    LocalTwoCrossFamCat 5 .suzuki := by
  rintro ⟨d, hv⟩ ⟨m, hd⟩ _ _
  change d = _ at hd
  subst hd
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.suzukiModel_cat hv
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  by_cases ha2 : a = 2
  · subst ha2
    exact IsLocallyBalancedAbs.of_mulEquiv e
      (isLocallyBalancedAbs_two_suzukiGroup_thirtyTwo (by simpa using hF'))
  · exact IsLocallyBalancedAbs.of_mulEquiv e
      (isLocallyBalancedAbs_two_suzukiGroup_odd ha hF' (by norm_num) (by norm_num)
        fun h => absurd h ha2)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
