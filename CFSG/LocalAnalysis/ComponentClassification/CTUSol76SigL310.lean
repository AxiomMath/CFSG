module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSep
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigWG

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

omit [Finite G] in
theorem orderOf_inv_mul_mul (m s : G) : orderOf (m⁻¹ * s * m) = orderOf s := by
  have h := (MulAut.conj m⁻¹).orderOf_eq s
  simp only [MulAut.conj_apply, inv_inv] at h
  exact h

theorem isElemAbelian_sup_zpowers_two {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    {s : G} (hs2 : orderOf s = 2) (hsE : s ∉ E) (hsc : s ∈ centralizer (E : Set G)) :
    CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers s) ∧
      Nat.card (E ⊔ zpowers s : Subgroup G) = 2 * Nat.card E := by
  have hzs : zpowers s ≤ centralizer (E : Set G) := zpowers_le.mpr hsc
  have hEz : E ≤ centralizer ((zpowers s : Subgroup G) : Set G) := le_centralizer_iff.mp hzs
  have hEc : E ≤ centralizer (E : Set G) := le_centralizer_iff_isMulCommutative.mpr hE.1
  have hzc : zpowers s ≤ centralizer ((zpowers s : Subgroup G) : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hA : E ⊔ zpowers s ≤ centralizer ((E ⊔ zpowers s : Subgroup G) : Set G) :=
    sup_le (le_centralizer_iff.mp (sup_le hEc hzs)) (le_centralizer_iff.mp (sup_le hEz hzc))
  have hs : s ^ 2 = 1 := by rw [← hs2]; exact pow_orderOf_eq_one s
  refine ⟨⟨le_centralizer_iff_isMulCommutative.mp hA, fun x hx => ?_⟩, ?_⟩
  · have hx' : x ∈ (E : Set G) * (zpowers s : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left E (zpowers s)
        (hzs.trans (Subgroup.centralizer_le_normalizer (E : Set G)))]
      exact hx
    obtain ⟨a, ha, z, hz, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    have hcomm : Commute a (s ^ k) :=
      Commute.zpow_right (show Commute a s from (mem_centralizer_iff.mp hsc) a ha) k
    rw [hcomm.mul_pow, hE.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hs, one_zpow]
  · have hprod := AS81.card_sup_mul_card_inf_of_le_normalizer_left
      (hzs.trans (Subgroup.centralizer_le_normalizer (E : Set G)))
    have hbot : zpowers s ⊓ E = ⊥ := by
      have hdvd : Nat.card (zpowers s ⊓ E : Subgroup G) ∣ 2 := by
        rw [← hs2, ← Nat.card_zpowers]
        exact card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact card_eq_one.mp h
      · exfalso
        have heq : zpowers s ⊓ E = zpowers s :=
          eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [h, Nat.card_zpowers, hs2]))
        have hmem : s ∈ zpowers s ⊓ E := by
          rw [heq]
          exact mem_zpowers s
        exact hsE (mem_inf.mp hmem).2
    rw [hbot, card_bot, mul_one, Nat.card_zpowers, hs2, sup_comm] at hprod
    exact hprod

theorem le_sup_of_mem_pumpSet (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {t : G} (htK' : t ∈ K') (ht2 : orderOf t = 2) {J : Subgroup G}
    (hJ : J ∈ pumpSet K (centralizer ({t} : Set G))) :
    J ≤ twoLayerIn (K ⊓ centralizer ({t} : Set G)) ⊔ oddCoreIn (centralizer ({t} : Set G)) := by
  obtain ⟨M, hM, hsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK hK' hne htK' ht2
  obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp (ncard_pumpSet_eq_one hq hR1 hG hN hK hK' hne htK' ht2)
  rw [hM', Set.mem_singleton_iff] at hJ hM
  rw [hJ, ← hM]
  calc M ≤ M ⊔ oddCoreIn (twoLayerIn (centralizer ({t} : Set G))) := le_sup_left
    _ = _ := hsup.symm
    _ ≤ _ := sup_le_sup_left (oddCoreIn_le_of_le_normalizer (map_subtype_le _)
        (le_normalizer_twoLayerIn _)) _

theorem le_coreActionKernel_of_not_mem_pumpSet {C J : Subgroup G}
    (h212 : twoLayerIn (K ⊓ C) ≤ solomonKStarOf C) (hJ : IsTwoComponentIn J C)
    (hJp : J ∉ pumpSet K C) : twoLayerIn (K ⊓ C) ≤ coreActionKernel J := by
  by_contra hY
  by_cases hJs : J ∈ solomonKStar G
  · exact hJp ⟨⟨hJ, hJs⟩, hY⟩
  · apply hY
    refine h212.trans (iSup₂_le fun J' hJ' => ?_)
    exact GSThmB.B5a.le_coreActionKernel_of_ne hJ.1 hJ'.1.1 hJ.2 hJ'.1.2
      fun h => hJs (h ▸ hJ'.2)

theorem twoLayerIn_centralizer_le_of_mem_right (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {E X : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) {s : G} (hsK' : s ∈ K')
    (hs2 : orderOf s = 2) (hEs : E ≤ centralizer ({s} : Set G))
    (hX : normalizer (E : Set G) ⊓ normalizer ((zpowers s : Subgroup G) : Set G) ≤ X)
    (hKX : K ≤ X) (hOX : oddCoreIn (centralizer ({s} : Set G)) ≤ X) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ X := by
  have hsQ : s ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm hsK'
  obtain ⟨-, -, -, h212, -⟩ := pump_facts hK hsQ hs2
  have hE2 := isPGroup_of_isKleinFour hE
  have hEY := le_pump_of_isPGroup hK hsQ hs2 hE2 (le_inf hEK hEs)
  refine twoLayerIn_le_of_forall fun J hJ => ?_
  by_cases hJp : J ∈ pumpSet K (centralizer ({s} : Set G))
  · exact (le_sup_of_mem_pumpSet hq hR1 hG hN hK hK' hne hsK' hs2 hJp).trans
      (sup_le (((map_subtype_le _).trans inf_le_left).trans hKX) hOX)
  have hEJ : E ≤ coreActionKernel J :=
    hEY.trans (le_coreActionKernel_of_not_mem_pumpSet h212 hJ hJp)
  refine (inf_centralizer_sup_oddCoreIn_eq hE2 hEJ).symm.le.trans
    (sup_le (fun x hx => hX ⟨Subgroup.centralizer_le_normalizer (E : Set G) hx.2, ?_⟩)
      ((oddCoreIn_le_of_isTwoComponentIn hJ).trans hOX))
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [centralizer_zpowers_eq]
  exact hJ.1 hx.1

theorem twoLayerIn_centralizer_le_of_mem_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    {E V X : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hEV : E ≤ centralizer (V : Set G)) {v : G} (hvV : v ∈ V)
    (hX : normalizer (E : Set G) ⊓ centralizer ({v} : Set G) ≤ X) (hKX : K ≤ X) (hK'X : K' ≤ X)
    {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N) (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K')
    {s : G} (hsK'' : s ∈ K'') (hs2 : orderOf s = 2) (hEs : E ≤ centralizer ({s} : Set G))
    (hVs : V ≤ centralizer ({s} : Set G)) (hOX : oddCoreIn (centralizer ({s} : Set G)) ≤ X) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ X := by
  have hsQ : s ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK'' hK hK''K hsK''
  have hsQ' : s ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK'' hK' hK''K' hsK''
  obtain ⟨-, -, -, h212, -⟩ := pump_facts hK hsQ hs2
  obtain ⟨-, -, -, h212', -⟩ := pump_facts hK' hsQ' hs2
  have hE2 := isPGroup_of_isKleinFour hE
  have hV2 := isPGroup_of_isKleinFour hV
  have hEY := le_pump_of_isPGroup hK hsQ hs2 hE2 (le_inf hEK hEs)
  have hVY := le_pump_of_isPGroup hK' hsQ' hs2 hV2 (le_inf hVK' hVs)
  refine twoLayerIn_le_of_forall fun J hJ => ?_
  by_cases hJp : J ∈ pumpSet K (centralizer ({s} : Set G))
  · exact (le_sup_of_mem_pumpSet hq hR1 hG hN hK hK'' hK''K.symm hsK'' hs2 hJp).trans
      (sup_le (((map_subtype_le _).trans inf_le_left).trans hKX) hOX)
  by_cases hJp' : J ∈ pumpSet K' (centralizer ({s} : Set G))
  · exact (le_sup_of_mem_pumpSet hq hR1 hG hN hK' hK'' hK''K'.symm hsK'' hs2 hJp').trans
      (sup_le (((map_subtype_le _).trans inf_le_left).trans hK'X) hOX)
  have hSJ : E ⊔ V ≤ coreActionKernel J :=
    sup_le (hEY.trans (le_coreActionKernel_of_not_mem_pumpSet h212 hJ hJp))
      (hVY.trans (le_coreActionKernel_of_not_mem_pumpSet h212' hJ hJp'))
  have hS2 := isPGroup_sup_of_le_centralizer hE2 hV2 hEV
  refine (inf_centralizer_sup_oddCoreIn_eq hS2 hSJ).symm.le.trans
    (sup_le (fun x hx => hX ⟨?_, ?_⟩) ((oddCoreIn_le_of_isTwoComponentIn hJ).trans hOX))
  · exact Subgroup.centralizer_le_normalizer (E : Set G)
      (centralizer_le (by exact_mod_cast le_sup_left) hx.2)
  · exact centralizer_le (Set.singleton_subset_iff.mpr (le_sup_right (a := E) hvV)) hx.2

theorem twoLayerIn_centralizer_le_of_mem_left (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V X : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {v : G} (hvV : v ∈ V)
    (hv1 : v ≠ 1) (hLv : twoLayerIn (centralizer ({v} : Set G)) ≤ X) (hK'X : K' ≤ X) {s : G}
    (hsK : s ∈ K) (hs2 : orderOf s = 2) (hVs : V ≤ centralizer ({s} : Set G))
    (hOX : oddCoreIn (centralizer ({s} : Set G)) ≤ X) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsQ : s ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' hne hsK
  obtain ⟨-, -, -, h212, -⟩ := pump_facts hK' hsQ hs2
  have hV2 := isPGroup_of_isKleinFour hV
  have hVY := le_pump_of_isPGroup hK' hsQ hs2 hV2 (le_inf hVK' hVs)
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hvV hv1
  have hsv : s ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hVs hvV)).symm
  have hbal : twoLayerIn (centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G)) ≤
      twoLayerIn (centralizer ({v} : Set G)) := by
    have h := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({v} : Set G))
      (A := zpowers s) (zpowers_le.mpr hsv)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one]))
    rw [centralizer_zpowers_eq] at h
    exact h
  refine twoLayerIn_le_of_forall fun J hJ => ?_
  by_cases hJp : J ∈ pumpSet K' (centralizer ({s} : Set G))
  · exact (le_sup_of_mem_pumpSet hq hR1 hG hN hK' hK hne.symm hsK hs2 hJp).trans
      (sup_le (((map_subtype_le _).trans inf_le_left).trans hK'X) hOX)
  have hvJ : v ∈ coreActionKernel J :=
    (hVY.trans (le_coreActionKernel_of_not_mem_pumpSet h212 hJ hJp)) hvV
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    isQuasisimple_quotient_of_isPComponent hJ.1 hJ.2
  have hsupY : (J ⊓ centralizer ({v} : Set G)) ⊔ oddCoreIn J = J := by
    have h := inf_centralizer_sup_oddCoreIn_eq
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])) (zpowers_le.mpr hvJ)
    rwa [centralizer_zpowers_eq] at h
  obtain ⟨hR2, -, hRsup, -⟩ := cover_facts hJq inf_le_left hsupY
  have hYC : J ⊓ centralizer ({v} : Set G) ≤
      centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hJ.1)
  have hsub : ((J ⊓ centralizer ({v} : Set G)).subgroupOf
      (centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G))).IsSubnormal := by
    have h0 : (J.subgroupOf (centralizer ({s} : Set G))).IsSubnormal :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJ.1).mp hJ.2).1
    have h1 := isSubnormal_subgroupOf_of_le
      (inf_le_right : centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G) ≤ _) h0
    convert h1 using 1
    ext x
    simp only [mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).1⟩⟩
  have hRC : IsTwoComponentIn (oddResidualIn (J ⊓ centralizer ({v} : Set G)))
      (centralizer ({v} : Set G) ⊓ centralizer ({s} : Set G)) :=
    ⟨hR2.1.trans hYC, GrSLit.isPComponent_subgroupOf_of_isSubnormal hR2.1 hYC hsub hR2.2⟩
  calc J = oddResidualIn (J ⊓ centralizer ({v} : Set G)) ⊔ oddCoreIn J := hRsup.symm
    _ ≤ X := sup_le ((le_twoLayerIn_of_isTwoComponentIn hRC).trans (hbal.trans hLv))
        ((oddCoreIn_le_of_isTwoComponentIn hJ).trans hOX)

theorem twoLayerIn_centralizer_le_of_conj {X : Subgroup G} {g s : G} (hg : g ∈ X)
    (h : twoLayerIn (centralizer ({g⁻¹ * s * g} : Set G)) ≤ X) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ X := by
  have h1 := map_centralizer_singleton (MulAut.conj g) (g⁻¹ * s * g)
  have h2 : (MulAut.conj g) (g⁻¹ * s * g) = s := by rw [MulAut.conj_apply]; group
  rw [h2] at h1
  have h3 := map_twoLayerIn (MulAut.conj g) (centralizer ({g⁻¹ * s * g} : Set G))
  rw [h1] at h3
  calc twoLayerIn (centralizer ({s} : Set G))
      = (twoLayerIn (centralizer ({g⁻¹ * s * g} : Set G))).map (MulAut.conj g).toMonoidHom :=
        h3.symm
    _ ≤ X.map (MulAut.conj g).toMonoidHom := map_mono h
    _ = X := mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)

theorem oddCoreIn_centralizer_le_normalizer_wGroup (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) {s : G} (hBs : B ≤ centralizer ({s} : Set G))
    (hVs : V ≤ centralizer ({s} : Set G)) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) :=
  le_normalizer_wGroup_of_odd_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hB8
    (coprime_card_oddCoreIn _) (hBs.trans (le_normalizer_oddCoreIn _))
    (hVs.trans (le_normalizer_oddCoreIn _))

theorem oddCoreIn_centralizer_le_of_mem_rank_three (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V A F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hAQ : A ≤ coreActionKernel K') (hAV : A ≤ centralizer (V : Set G))
    (hA : CFSG.Open.IsElemAbelian 2 A) (hA8 : Nat.card A = 8) (hF : IsKleinFour F) (hFA : F ≤ A)
    (hFK : F ≤ K) {s : G} (hsA : s ∈ A) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup F V : Set G) := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  rw [wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hA hF hFA hFK hF hFA]
  exact oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hA hA8
    hF hFA hFK (fun a ha => mem_centralizer_singleton_iff.mpr (hAc a ha s hsA))
    (le_centralizer_singleton_of_mem hAV hsA)

theorem oddCoreIn_centralizer_le_of_mem_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N)
    (hK''K' : K'' ≠ K') {s : G} (hsK'' : s ∈ K'') (hs2 : orderOf s = 2)
    (hEs : E ≤ centralizer ({s} : Set G)) (hVs : V ≤ centralizer ({s} : Set G)) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  by_cases hsE : s ∈ E
  · exact oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
      hB8 hE hEB hEK (fun b hb => mem_centralizer_singleton_iff.mpr (hBc b hb s (hEB hsE))) hVs
  have hsc : s ∈ centralizer (E : Set G) := mem_centralizer_iff.mpr fun e he =>
    mem_centralizer_singleton_iff.mp (hEs he)
  obtain ⟨hAe, hA8⟩ :=
    isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hE) hs2 hsE hsc
  have hsQ : s ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK'' hK' hK''K' hsK''
  have hAQ : E ⊔ zpowers s ≤ coreActionKernel K' := sup_le (hEB.trans hBQ) (zpowers_le.mpr hsQ)
  have hsV : s ∈ centralizer (V : Set G) := mem_centralizer_iff.mpr fun w hw =>
    mem_centralizer_singleton_iff.mp (hVs hw)
  have hAV : E ⊔ zpowers s ≤ centralizer (V : Set G) :=
    sup_le (hEB.trans hBV) (zpowers_le.mpr hsV)
  have hW : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  rw [← hW]
  exact oddCoreIn_centralizer_le_of_mem_rank_three hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hAe
    (by rw [hA8, hE.card_four]) hE le_sup_left hEK (mem_sup_right (mem_zpowers s))

theorem twoLayerIn_centralizer_le_of_mem_V (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G)) {v : G}
    (hvV : v ∈ V) (hv1 : v ≠ 1) :
    twoLayerIn (centralizer ({v} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hvV hv1
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hVc := comm_of_isKleinFour hV
  have hWv : wGroup E (zpowers v) = wGroup B V := by
    rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV hVK' hE hEK hEV hvV hv1]
    exact wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hBv : B ≤ centralizer ({v} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBV hb)) v hvV).symm
  have hEv : E ≤ centralizer ({v} : Set G) := hEB.trans hBv
  refine twoLayerIn_centralizer_le_of_mem_right hq hR1 hG hN hK hK' hne hE hEK (hVK' hvV) hv2 hEv
    (fun g hg => ?_) hKW
    (oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE
      hEB hEK hBv (fun w hw => mem_centralizer_singleton_iff.mpr (hVc w hw v hvV)))
  rw [← hWv]
  exact le_normalizer_wGroup hg.1 hg.2

theorem twoLayerIn_centralizer_le_of_mem_E (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G))
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {e : G} (heB : e ∈ B) (heK : e ∈ K)
    (he2 : orderOf e = 2) :
    twoLayerIn (centralizer ({e} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hVe : V ≤ centralizer ({e} : Set G) := le_centralizer_singleton_of_mem hBV heB
  exact twoLayerIn_centralizer_le_of_mem_left hq hR1 hG hN hK hK' hne hV hVK' hvV hv1
    (twoLayerIn_centralizer_le_of_mem_V hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB hEK
      hKW hvV hv1) hK'W heK he2 hVe
    (oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE
      hEB hEK (fun b hb => mem_centralizer_singleton_iff.mpr (hBc b hb e heB)) hVe)

theorem twoLayerIn_centralizer_le_of_mem_kStar_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G))
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {K'' : Subgroup G}
    (hK'' : K'' ∈ kStarComponents N) (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K')
    (hK''W : K'' ≤ normalizer (wGroup B V : Set G)) {s : G} (hsK'' : s ∈ K'')
    (hs2 : orderOf s = 2) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have hE2 := isPGroup_of_isKleinFour hE
  have hV2 := isPGroup_of_isKleinFour hV
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hS2 := isPGroup_sup_of_le_centralizer hE2 hV2 hEV
  have hSQ : E ⊔ V ≤ coreActionKernel K'' :=
    sup_le (hEK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
      (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
  obtain ⟨m, hm, hmS⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ) hsK'' hs2
  have ht2 : orderOf (m⁻¹ * s * m) = 2 := by rw [orderOf_inv_mul_mul, hs2]
  refine twoLayerIn_centralizer_le_of_conj (hK''W hm) ?_
  generalize m⁻¹ * s * m = t at hmS ht2 ⊢
  obtain ⟨htK'', htS⟩ := mem_inf.mp hmS
  have hEt : E ≤ centralizer ({t} : Set G) := fun e he => mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp htS) e (le_sup_left (b := V) he))
  have hVt : V ≤ centralizer ({t} : Set G) := fun w hw => mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp htS) w (le_sup_right (a := E) hw))
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  exact twoLayerIn_centralizer_le_of_mem_third hq hR1 hG hN hK hK' hE hEK hV hVK' hEV hvV
    (fun g hg => le_normalizer_wGroup_of_mem_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE
      hEB hEK hE hEB hvV hv1 hg.1 hg.2) hKW hK'W hK'' hK''K hK''K' htK'' ht2 hEt hVt
    (oddCoreIn_centralizer_le_of_mem_third hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
      hEK hK'' hK''K' htK'' ht2 hEt hVt)

theorem twoLayerIn_centralizer_le_of_mem_kStar_right (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K)
    (hconn : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected)
    (hKW : K ≤ normalizer (wGroup B V : Set G)) (hK'W : K' ≤ normalizer (wGroup B V : Set G))
    {s : G} (hsK' : s ∈ K') (hs2 : orderOf s = 2) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  have hsupB := inf_centralizer_sup_oddCoreIn_eq hB2 hBQ
  obtain ⟨m, hm, hmB⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left hsupB hsK' hs2
  have ht2 : orderOf (m⁻¹ * s * m) = 2 := by rw [orderOf_inv_mul_mul, hs2]
  refine twoLayerIn_centralizer_le_of_conj (hK'W hm) ?_
  generalize m⁻¹ * s * m = t at hmB ht2 ⊢
  obtain ⟨htK', htB⟩ := mem_inf.mp hmB
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  have hBt : B ≤ centralizer ({t} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp htB) b hb)
  have hEt : E ≤ centralizer ({t} : Set G) := hEB.trans hBt
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hv2 := orderOf_eq_two_of_isKleinFour hV hvV hv1
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hvY : v ∈ K' ⊓ centralizer (E : Set G) := ⟨hVK' hvV, mem_centralizer_iff.mpr fun e he =>
    ((mem_centralizer_iff.mp (hEV he)) v hvV).symm⟩
  have htY : t ∈ K' ⊓ centralizer (E : Set G) := ⟨htK', mem_centralizer_iff.mpr fun e he =>
    mem_centralizer_singleton_iff.mp (hEt he)⟩
  have hWv : wGroup E (zpowers v) = wGroup B V := by
    rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV hVK' hE hEK hEV hvV hv1]
    exact wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hWt : wGroup E (zpowers t) = wGroup B V := by
    rw [← hWv]
    exact (wGroup_zpowers_eq_of_reachable h32 hG hN hK hK' hne hE hEK
      (hconn ⟨⟨v, hvY⟩, by rw [Subgroup.orderOf_mk]; exact hv2⟩
        ⟨⟨t, htY⟩, by rw [Subgroup.orderOf_mk]; exact ht2⟩)).symm
  have hrank : 2 ≤ CFSG.Open.pRank 2 (K' ⊓ centralizer (B : Set G)) :=
    (two_le_pRank_of_mem_solomonKStar hK'.2).trans (pRank_le_of_sup_oddCoreIn inf_le_left hsupB)
  obtain ⟨Vt, hVtY, hVt, htVt⟩ := exists_isKleinFour_mem hrank hmB ht2
  have hVtK' : Vt ≤ K' := hVtY.trans inf_le_left
  have hBVt : B ≤ centralizer (Vt : Set G) := fun b hb => mem_centralizer_iff.mpr fun w hw =>
    ((mem_centralizer_iff.mp (hVtY hw).2) b hb).symm
  have hWVt : wGroup B Vt = wGroup B V := by
    rw [← wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hVt hVtK' hBQ hBVt hB hE hEB hEK hE hEB,
      wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hVt hVtK' hE hEK (hEB.trans hBVt) htVt ht1]
    exact hWt
  have hVtc := comm_of_isKleinFour hVt
  have hOX : oddCoreIn (centralizer ({t} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
    rw [← hWVt]
    exact oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hK hK' hne hVt hVtK' hBQ hBVt hB
      hB8 hE hEB hEK hBt (fun w hw => mem_centralizer_singleton_iff.mpr (hVtc w hw t htVt))
  refine twoLayerIn_centralizer_le_of_mem_right hq hR1 hG hN hK hK' hne hE hEK htK' ht2 hEt
    (fun g hg => ?_) hKW hOX
  rw [← hWt]
  exact le_normalizer_wGroup hg.1 hg.2

theorem twoLayerIn_centralizer_le_of_mem_kStar_left (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G))
    (hK'W : K' ≤ normalizer (wGroup B V : Set G))
    (hO : ∀ s ∈ K ⊓ centralizer (V : Set G), orderOf s = 2 →
      oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G))
    {s : G} (hsK : s ∈ K) (hs2 : orderOf s = 2) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  obtain ⟨m, hm, hmV⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hV2 hVQ) hsK hs2
  have ht2 : orderOf (m⁻¹ * s * m) = 2 := by rw [orderOf_inv_mul_mul, hs2]
  refine twoLayerIn_centralizer_le_of_conj (hKW hm) ?_
  generalize m⁻¹ * s * m = t at hmV ht2 ⊢
  have hVt : V ≤ centralizer ({t} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (mem_inf.mp hmV).2) w hw)
  obtain ⟨v, hvV, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  exact twoLayerIn_centralizer_le_of_mem_left hq hR1 hG hN hK hK' hne hV hVK' hvV hv1
    (twoLayerIn_centralizer_le_of_mem_V hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB hEK
      hKW hvV hv1) hK'W (mem_inf.mp hmV).1 ht2 hVt (hO t hmV ht2)

omit [Finite G] in
theorem oddCoreIn_centralizer_le_of_conj {X : Subgroup G} {g s : G} (hg : g ∈ X)
    (h : oddCoreIn (centralizer ({g⁻¹ * s * g} : Set G)) ≤ X) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ X := by
  have h1 := map_centralizer_singleton (MulAut.conj g) (g⁻¹ * s * g)
  have h2 : (MulAut.conj g) (g⁻¹ * s * g) = s := by rw [MulAut.conj_apply]; group
  rw [h2] at h1
  have h3 := map_oddCoreIn (MulAut.conj g) (centralizer ({g⁻¹ * s * g} : Set G))
  rw [h1] at h3
  calc oddCoreIn (centralizer ({s} : Set G))
      = (oddCoreIn (centralizer ({g⁻¹ * s * g} : Set G))).map (MulAut.conj g).toMonoidHom :=
        h3.symm
    _ ≤ X.map (MulAut.conj g).toMonoidHom := map_mono h
    _ = X := mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)

theorem oddCoreIn_centralizer_le_of_mem_kStar_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N)
    (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K') (hK''W : K'' ≤ normalizer (wGroup B V : Set G))
    {s : G} (hsK'' : s ∈ K'') (hs2 : orderOf s = 2) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  have hE2 := isPGroup_of_isKleinFour hE
  have hV2 := isPGroup_of_isKleinFour hV
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hS2 := isPGroup_sup_of_le_centralizer hE2 hV2 hEV
  have hSQ : E ⊔ V ≤ coreActionKernel K'' :=
    sup_le (hEK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
      (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
  obtain ⟨m, hm, hmS⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ) hsK'' hs2
  have ht2 : orderOf (m⁻¹ * s * m) = 2 := by rw [orderOf_inv_mul_mul, hs2]
  refine oddCoreIn_centralizer_le_of_conj (hK''W hm) ?_
  generalize m⁻¹ * s * m = t at hmS ht2 ⊢
  obtain ⟨htK'', htS⟩ := mem_inf.mp hmS
  have hEt : E ≤ centralizer ({t} : Set G) := fun e he => mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp htS) e (le_sup_left (b := V) he))
  have hVt : V ≤ centralizer ({t} : Set G) := fun w hw => mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp htS) w (le_sup_right (a := E) hw))
  exact oddCoreIn_centralizer_le_of_mem_third hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE
    hEB hEK hK'' hK''K' htK'' ht2 hEt hVt

theorem oddCoreIn_centralizer_le_of_mem_left_of_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F)
    {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N) (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K')
    (hK''W : K'' ≤ normalizer (wGroup B V : Set G)) {s : G}
    (hs : s ∈ K ⊓ centralizer (V : Set G)) (hs2 : orderOf s = 2) :
    oddCoreIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) := by
  classical
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hrank : 2 ≤ CFSG.Open.pRank 2 (K ⊓ centralizer (V : Set G)) :=
    (two_le_pRank_of_mem_solomonKStar hK.2).trans
      (pRank_le_of_sup_oddCoreIn inf_le_left (inf_centralizer_sup_oddCoreIn_eq hV2 hVQ))
  obtain ⟨F, hFX, hF, hsF⟩ := exists_isKleinFour_mem hrank hs hs2
  have hFK : F ≤ K := hFX.trans inf_le_left
  have hFV : F ≤ centralizer (V : Set G) := hFX.trans inf_le_right
  have hWF : wGroup F V = wGroup B V :=
    (wGroup_eq_of_reflTransGen h32 hG hN hK hK' hne hV hVK' (hconn F hF hFX)).trans
      (wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB)
  have hS2 := isPGroup_sup_of_le_centralizer (isPGroup_of_isKleinFour hF) hV2 hFV
  have hSQ : F ⊔ V ≤ coreActionKernel K'' :=
    sup_le (hFK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
      (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
  have hrank'' : 2 ≤ CFSG.Open.pRank 2 (K'' ⊓ centralizer ((F ⊔ V : Subgroup G) : Set G)) :=
    (two_le_pRank_of_mem_solomonKStar hK''.2).trans
      (pRank_le_of_sup_oddCoreIn inf_le_left (inf_centralizer_sup_oddCoreIn_eq hS2 hSQ))
  obtain ⟨u, hu, hu2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hrank'')
  obtain ⟨T, hTY, hT, -⟩ := exists_isKleinFour_mem hrank'' hu hu2
  by_cases hTF : T ≤ F
  ·
    have hTF' : T = F := eq_of_le_of_card_ge hTF (le_of_eq (by rw [hT.card_four, hF.card_four]))
    have hsT : s ∈ T := by rw [hTF']; exact hsF
    exact oddCoreIn_centralizer_le_of_mem_kStar_third hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB
      hB8 hE hEB hEK hK'' hK''K hK''K' hK''W ((hTY.trans inf_le_left) hsT) hs2
  obtain ⟨t, htT, htF⟩ : ∃ t ∈ T, t ∉ F := by
    by_contra h
    push Not at h
    exact hTF fun x hx => h x hx
  have ht1 : t ≠ 1 := fun h => htF (h ▸ F.one_mem)
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_isKleinFour hT htT ht1
  have htK'' : t ∈ K'' := (hTY.trans inf_le_left) htT
  have htS : t ∈ centralizer ((F ⊔ V : Subgroup G) : Set G) := (hTY.trans inf_le_right) htT
  have htF' : t ∈ centralizer (F : Set G) := centralizer_le (by exact_mod_cast le_sup_left) htS
  have htV : t ∈ centralizer (V : Set G) := centralizer_le (by exact_mod_cast le_sup_right) htS
  obtain ⟨hAe, hA8⟩ :=
    isElemAbelian_sup_zpowers_two (isElemAbelian_of_isKleinFour hF) ht2 htF htF'
  have hAQ : F ⊔ zpowers t ≤ coreActionKernel K' :=
    sup_le (hFK.trans (le_coreActionKernel_of_ne hK' hK hne.symm))
      (zpowers_le.mpr (mem_coreActionKernel_of_ne hK'' hK' hK''K' htK''))
  have hAV : F ⊔ zpowers t ≤ centralizer (V : Set G) := sup_le hFV (zpowers_le.mpr htV)
  rw [← hWF]
  exact oddCoreIn_centralizer_le_of_mem_rank_three hq hR1 hG hN hK hK' hne hV hVK' hAQ hAV hAe
    (by rw [hA8, hF.card_four]) hF le_sup_left hFK (mem_sup_left hsF)

theorem twoLayerIn_centralizer_le_of_mem_kStar_left_of_third (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F)
    (hKW : K ≤ normalizer (wGroup B V : Set G)) (hK'W : K' ≤ normalizer (wGroup B V : Set G))
    {K'' : Subgroup G} (hK'' : K'' ∈ kStarComponents N) (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K')
    (hK''W : K'' ≤ normalizer (wGroup B V : Set G)) {s : G} (hsK : s ∈ K)
    (hs2 : orderOf s = 2) :
    twoLayerIn (centralizer ({s} : Set G)) ≤ normalizer (wGroup B V : Set G) :=
  twoLayerIn_centralizer_le_of_mem_kStar_left hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
    hEK hKW hK'W (fun _ ht ht2 => oddCoreIn_centralizer_le_of_mem_left_of_third hq hR1 hG hN hK hK'
      hne hV hVK' hBQ hBV hB hB8 hE hEB hEK hconn hK'' hK''K hK''K' hK''W ht ht2) hsK hs2

end CFSG.ComponentClassification.Sol76.Sig
