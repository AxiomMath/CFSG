module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvPt
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39KC

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem nonempty_coreQuot_equiv_map_of_sup_eq {C M : Subgroup G}
    (hY2 : twoLayerIn (K ⊓ C) ⊔ oddCoreIn K = K) (hYL : twoLayerIn (K ⊓ C) ≤ twoLayerIn C)
    (hMC : IsTwoComponentIn M C)
    (hsup : twoLayerIn (K ⊓ C) ⊔ oddCoreIn (twoLayerIn C) = M ⊔ oddCoreIn (twoLayerIn C)) :
    Nonempty (coreQuot K ≃* ↥((M.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := twoLayerIn (K ⊓ C) with hYdef
  have hYKC : Y ≤ K ⊓ C := map_subtype_le _
  have hYK : Y ≤ K := hYKC.trans inf_le_left
  have hYC : Y ≤ C := hYKC.trans inf_le_right
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  set I := (M.subgroupOf C).map π with hI
  have hOLC : oddCoreIn (twoLayerIn C) ≤ C := (oddCoreIn_twoLayerIn_le C).trans (map_subtype_le _)
  have hπO : ∀ (o : G) (ho : o ∈ oddCoreIn (twoLayerIn C)), π ⟨o, hOLC ho⟩ = 1 := by
    intro o ho
    obtain ⟨o', ho', ho'o⟩ := oddCoreIn_twoLayerIn_le C ho
    have : (⟨o, hOLC ho⟩ : C) = o' := Subtype.ext ho'o.symm
    rw [this]
    exact (QuotientGroup.eq_one_iff o').mpr ho'
  have hLN : twoLayerIn C ≤ normalizer (oddCoreIn (twoLayerIn C) : Set G) :=
    le_normalizer_oddCoreIn (twoLayerIn C)
  have hMN : M ≤ normalizer (oddCoreIn (twoLayerIn C) : Set G) :=
    (le_twoLayerIn_of_isTwoComponentIn hMC).trans hLN
  have hYN : Y ≤ normalizer (oddCoreIn (twoLayerIn C) : Set G) := hYL.trans hLN
  set ψ : ↥Y →* coreQuot K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hYK) with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) q
    have hk : (k : G) ∈ oddCoreIn K ⊔ Y := by rw [sup_comm, hY2]; exact k.2
    obtain ⟨o, ho, y, hy, hoy⟩ :=
      exists_mul_of_mem_sup_normalizer (hYK.trans (le_normalizer_oddCoreIn K)) hk
    obtain ⟨o', ho', ho'o⟩ := ho
    refine ⟨⟨y, hy⟩, ?_⟩
    have ho'o' : (o' : G) = o := ho'o
    have hk' : k = o' * Subgroup.inclusion hYK ⟨y, hy⟩ := Subtype.ext (by
      rw [Subgroup.coe_mul, ho'o']
      exact hoy)
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) o' = 1 := (QuotientGroup.eq_one_iff o').mpr ho'
    rw [hk', map_mul, h1, one_mul]
    rfl
  have hψodd : Odd (Nat.card ψ.ker) :=
    odd_card_ker_mk_comp_inclusion hYK (pPrimeCore 2 ↥K)
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hmapY : ∀ y : ↥Y, (π.comp (Subgroup.inclusion hYC)) y ∈ I := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ oddCoreIn (twoLayerIn C) ⊔ M := by
      rw [sup_comm, ← hsup]
      exact mem_sup_left hy
    obtain ⟨o, ho, m, hm, hom⟩ := exists_mul_of_mem_sup_normalizer hMN hy'
    have hyom : (Subgroup.inclusion hYC ⟨y, hy⟩ : C) = ⟨o, hOLC ho⟩ * ⟨m, hMC.1 hm⟩ :=
      Subtype.ext hom
    show π (Subgroup.inclusion hYC ⟨y, hy⟩) ∈ I
    rw [hyom, map_mul, hπO o ho, one_mul]
    exact ⟨⟨m, hMC.1 hm⟩, (Subgroup.mem_subgroupOf).mpr hm, rfl⟩
  set φ : ↥Y →* ↥I := (π.comp (Subgroup.inclusion hYC)).codRestrict I hmapY with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨x, ⟨m, hm, rfl⟩⟩
    have hm' : (m : G) ∈ oddCoreIn (twoLayerIn C) ⊔ Y := by
      rw [sup_comm, hsup]
      exact mem_sup_left ((Subgroup.mem_subgroupOf).mp hm)
    obtain ⟨o, ho, y, hy, hoy⟩ := exists_mul_of_mem_sup_normalizer hYN hm'
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    have hmoy : m = ⟨o, hOLC ho⟩ * Subgroup.inclusion hYC ⟨y, hy⟩ := Subtype.ext hoy
    show π (Subgroup.inclusion hYC ⟨y, hy⟩) = π m
    rw [hmoy, map_mul, hπO o ho, one_mul]
  have hφodd : Odd (Nat.card φ.ker) := by
    rw [hφ, MonoidHom.ker_codRestrict]
    exact odd_card_ker_mk_comp_inclusion hYC (pPrimeCore 2 ↥C)
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hIO : pPrimeCore 2 ↥I = ⊥ := by
    obtain ⟨K'', hK'', -, hMK'', -⟩ := hMC.2
    rw [hI, hMK'']
    have h := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hK''.2
    rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥C) 2, le_bot_iff,
      map_eq_bot_iff_of_injective _ (subtype_injective _)] at h
    exact h
  exact ⟨((coreQuotEquivOfSurjective ψ hψs hψodd).trans (coreQuotCoreQuotEquiv ↥K)).symm.trans
    ((coreQuotEquivOfSurjective φ hφs hφodd).trans (coreQuotEquivSelf hIO))⟩

theorem oddCoreIn_inf_le_of_involutionCoreFreeInv (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFreeInv (coreQuot K))
    {v : G} (hvK' : v ∈ K') (hv2 : orderOf v = 2) {V₁ : Subgroup G} (hV₁ : IsKleinFour V₁)
    (hV₁K' : V₁ ≤ K') (hV₁v : V₁ ≤ centralizer ({v} : Set G))
    {e : G} (heK : e ∈ K) (he2 : orderOf e = 2) (hve : e * v = v * e) :
    oddCoreIn (centralizer ({e} : Set G)) ⊓ centralizer ({v} : Set G) ≤
      oddCoreIn (centralizer ({v} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cv := centralizer ({v} : Set G) with hCv
  set X := oddCoreIn (centralizer ({e} : Set G)) ⊓ Cv with hXdef
  have hvQ : v ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm hvK'
  have hP := conjClosure_le_of_isKleinFour hq hR1 hG hN hK hK' hne hvQ hv2 hV₁ hV₁K' hV₁v
  obtain ⟨M, hM, hsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK hK' hne hvK' hv2
  have hTe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hv2)
  have hSe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two he2)
  have hS1 := zpowers_ne_bot_of_orderOf_eq_two he2
  have hT1 := zpowers_ne_bot_of_orderOf_eq_two hv2
  have hev : e ∈ Cv := mem_centralizer_singleton_iff.mpr hve
  have hST : zpowers e ≤ centralizer ((zpowers v : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact zpowers_le.mpr hev
  have h25 := sol25 hS1 hT1 hSe hTe hST
  rw [centralizer_zpowers_eq, centralizer_zpowers_eq] at h25
  have hX' : X ≤ oddCoreIn (centralizer ((zpowers e : Subgroup G) : Set G)) ⊓
      centralizer ((zpowers v : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq, centralizer_zpowers_eq]
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_oddCoreIn _))
  have heKv : e ∈ twoLayerIn (K ⊓ Cv) :=
    mem_pump_of_two hK hvQ hv2 ⟨heK, hev⟩ (k := 1) (by rw [he2, pow_one])
  have heM : e ∈ oddCoreIn Cv ⊔ M := by
    have h1 : e ∈ M ⊔ oddCoreIn (twoLayerIn Cv) := by
      rw [← hsup]; exact mem_sup_left heKv
    have h2 : M ⊔ oddCoreIn (twoLayerIn Cv) ≤ oddCoreIn Cv ⊔ M :=
      sup_le le_sup_right ((oddCoreIn_twoLayerIn_le Cv).trans le_sup_left)
    exact h2 h1
  have hMC : IsTwoComponentIn M Cv := hM.1.1
  obtain ⟨-, hYO, -, h212, -⟩ := pump_facts hK hvQ hv2
  obtain ⟨ι⟩ := nonempty_coreQuot_equiv_map_of_sup_eq hYO
    (h212.trans (solomonKStarOf_le_twoLayerIn Cv)) hMC hsup
  have hfreeM := isInvolutionCoreFreeInv_of_mulEquiv ι hfree
  have hkey : ⁅M, X⁆ ≤ oddCoreIn Cv :=
    commutator_le_oddCoreIn_of_involutionCoreFreeInv hMC.1 hMC.2 hfreeM heM
      (by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two he2)
  have hCO : Cv ≤ normalizer (oddCoreIn Cv : Set G) := le_normalizer_oddCoreIn Cv
  refine le_oddCoreIn_of_commutator_le inf_le_right hXodd h25.1 fun M' hM' => ?_
  have hM'' : IsTwoComponentIn M' (centralizer ((zpowers v : Subgroup G) : Set G)) := by
    rw [centralizer_zpowers_eq]; exact hM'
  rcases pump_moves_of_le hK hvQ hv2 hP hM' with h | h
  · have heM' : zpowers e ≤ coreActionKernel M' := zpowers_le.mpr (h heKv)
    have h1 := commutator_le_oddCoreIn_of_not_moves hS1 hT1 hSe hTe hST hM'' hX'
      (Or.inr ((Subgroup.commutator_mono le_rfl inf_le_left).trans
        (commutator_le_oddCoreIn_of_le_coreActionKernel heM')))
    exact h1.trans (oddCoreIn_le_of_isTwoComponentIn hM')
  · have h' : M' ≤ oddCoreIn (twoLayerIn Cv) ⊔ M := by
      rw [sup_comm, hsup, sup_comm] at h
      exact h
    have hML : M ≤ twoLayerIn Cv := le_twoLayerIn_of_isTwoComponentIn hMC
    have hOL : oddCoreIn (twoLayerIn Cv) ≤ Cv := (map_subtype_le _).trans (map_subtype_le _)
    refine (Subgroup.commutator_mono h' le_rfl).trans ?_
    refine commutator_sup_le_of_le (hML.trans (le_normalizer_oddCoreIn _)) (hOL.trans hCO)
      (hMC.1.trans hCO) ?_ hkey
    exact (Subgroup.commutator_mono (oddCoreIn_twoLayerIn_le Cv) le_rfl).trans
      (CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _
        (inf_le_right.trans hCO))

theorem theta_eq_oddCoreIn_of_involutionCoreFreeInv (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFreeInv (coreQuot K))
    {V₁ : Subgroup G} (hV₁ : IsKleinFour V₁) (hV₁K' : V₁ ≤ K') {e : G} (heK : e ∈ K)
    (he2 : orderOf e = 2) (hV₁e : V₁ ≤ centralizer ({e} : Set G)) :
    theta V₁ e = oddCoreIn (centralizer ({e} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (theta_le_oddCoreIn hV₁e) ?_
  set Oe := oddCoreIn (centralizer ({e} : Set G)) with hOe
  have hV2 := isPGroup_of_isKleinFour hV₁
  have hVc := comm_of_isKleinFour hV₁
  have hVOe : V₁ ≤ normalizer (Oe : Set G) := hV₁e.trans (le_normalizer_oddCoreIn _)
  have hcop : Nat.Coprime 2 (Nat.card Oe) := coprime_card_oddCoreIn _
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two V₁ Oe hV2 hVOe hcop
  rw [← hfac]
  refine sup_le le_sup_left ?_
  obtain ⟨v, hv, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV₁
  have hv2 := orderOf_eq_two_of_isKleinFour hV₁ hv hv1
  have hV₁v : V₁ ≤ centralizer ({v} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (hVc w hw v hv)
  have hve : e * v = v * e := (mem_centralizer_singleton_iff.mp (hV₁e hv)).symm
  have hcrux := oddCoreIn_inf_le_of_involutionCoreFreeInv hq hR1 hG hN hK hK' hne hfree
    (hV₁K' hv) hv2 hV₁ hV₁K' hV₁v heK he2 hve
  intro w hw
  have hwOe : w ∈ Oe := (mem_inf.mp hw).1
  have hwV : w ∈ centralizer (V₁ : Set G) := (mem_inf.mp hw).2
  have hwv : w ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hwV) v hv).symm
  have h1 : w ∈ oddCoreIn (centralizer ({v} : Set G)) := hcrux (mem_inf.mpr ⟨hwOe, hwv⟩)
  have hCV : centralizer (V₁ : Set G) ≤
      normalizer (oddCoreIn (centralizer ({v} : Set G)) : Set G) :=
    (centralizer_le (Set.singleton_subset_iff.mpr hv)).trans (le_normalizer_oddCoreIn _)
  exact mem_sup_right (mem_inf.mpr ⟨hwOe,
    inf_le_oddCoreIn (coprime_card_oddCoreIn _) hCV (mem_inf.mpr ⟨h1, hwV⟩)⟩)

theorem wGroup_eq_iSup_of_involutionCoreFreeInv (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFreeInv (coreQuot K))
    {E V₁ : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) (hV₁ : IsKleinFour V₁)
    (hV₁K' : V₁ ≤ K') (hEV₁ : E ≤ centralizer (V₁ : Set G)) :
    wGroup E V₁ = ⨆ (e : G) (_ : e ∈ E) (_ : e ≠ 1), oddCoreIn (centralizer ({e} : Set G)) := by
  refine iSup_congr fun e => iSup_congr fun he => iSup_congr fun he1 => ?_
  have hV₁e : V₁ ≤ centralizer ({e} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV₁ he)) w hw)
  exact theta_eq_oddCoreIn_of_involutionCoreFreeInv hq hR1 hG hN hK hK' hne hfree hV₁ hV₁K'
    (hEK he) (orderOf_eq_two_of_isKleinFour hE he he1) hV₁e

theorem iSup_oddCoreIn_eq_of_involutionCoreFreeInv (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFreeInv (coreQuot K))
    (hfree' : IsInvolutionCoreFreeInv (coreQuot K'))
    {E V : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hEV : E ≤ centralizer (V : Set G)) :
    (⨆ (e : G) (_ : e ∈ E) (_ : e ≠ 1), oddCoreIn (centralizer ({e} : Set G))) =
      ⨆ (v : G) (_ : v ∈ V) (_ : v ≠ 1), oddCoreIn (centralizer ({v} : Set G)) := by
  have hEc := comm_of_isKleinFour hE
  have hVc := comm_of_isKleinFour hV
  have hEe : CFSG.Assembly.IsElemAbelian 2 E := isElemAbelian_of_isKleinFour hE
  have hVe : CFSG.Assembly.IsElemAbelian 2 V := isElemAbelian_of_isKleinFour hV
  have hE4 : 2 ^ 2 ≤ Nat.card E := by rw [hE.card_four]; norm_num
  have hV4 : 2 ^ 2 ≤ Nat.card V := by rw [hV.card_four]; norm_num
  have hcomm : ∀ e ∈ E, ∀ v ∈ V, e * v = v * e := fun e he v hv =>
    ((mem_centralizer_iff.mp (hEV he)) v hv).symm
  apply le_antisymm
  · refine iSup₂_le fun e he => iSup_le fun he1 => ?_
    have he2 := orderOf_eq_two_of_isKleinFour hE he he1
    have hVe' : V ≤ normalizer (oddCoreIn (centralizer ({e} : Set G)) : Set G) := fun v hv =>
      le_normalizer_oddCoreIn _ (mem_centralizer_singleton_iff.mpr (hcomm e he v hv).symm)
    refine CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_le Nat.prime_two hVe hV4 hVe'
      (coprime_card_oddCoreIn _) fun v hv hv1 => ?_
    have hv2 := orderOf_eq_two_of_isKleinFour hV hv hv1
    have hVv : V ≤ centralizer ({v} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr (hVc w hw v hv)
    refine (oddCoreIn_inf_le_of_involutionCoreFreeInv hq hR1 hG hN hK hK' hne hfree (hVK' hv) hv2
      hV hVK' hVv (hEK he) he2 (hcomm e he v hv)).trans ?_
    exact le_iSup₂_of_le v hv (le_iSup_of_le hv1 le_rfl)
  · refine iSup₂_le fun v hv => iSup_le fun hv1 => ?_
    have hv2 := orderOf_eq_two_of_isKleinFour hV hv hv1
    have hEv : E ≤ normalizer (oddCoreIn (centralizer ({v} : Set G)) : Set G) := fun e he =>
      le_normalizer_oddCoreIn _ (mem_centralizer_singleton_iff.mpr (hcomm e he v hv))
    refine CFSG.RankThree.PartTwo.Sec5.le_of_forall_inf_centralizer_le Nat.prime_two hEe hE4 hEv
      (coprime_card_oddCoreIn _) fun e he he1 => ?_
    have he2 := orderOf_eq_two_of_isKleinFour hE he he1
    have hEe' : E ≤ centralizer ({e} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr (hEc w hw e he)
    refine (oddCoreIn_inf_le_of_involutionCoreFreeInv hq hR1 hG hN hK' hK hne.symm hfree'
      (hEK he) he2 hE hEK hEe' (hVK' hv) hv2 (hcomm e he v hv).symm).trans ?_
    exact le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)

theorem le_normalizer_wGroup_of_involutionCoreFreeInv_both (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFreeInv (coreQuot K))
    (hfree' : IsInvolutionCoreFreeInv (coreQuot K'))
    {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N) :
    K ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hW : wGroup B V =
      ⨆ (v : G) (_ : v ∈ V) (_ : v ≠ 1), oddCoreIn (centralizer ({v} : Set G)) := by
    rw [← hWE, wGroup_eq_iSup_of_involutionCoreFreeInv hq hR1 hG hN hK hK' hne hfree hE hEK hV
      hVK' hEV, iSup_oddCoreIn_eq_of_involutionCoreFreeInv hq hR1 hG hN hK hK' hne hfree hfree' hE
      hEK hV hVK' hEV]
  have hV2 : IsPGroup 2 V := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  rw [← inf_centralizer_sup_oddCoreIn_eq hV2 hVQ]
  refine sup_le ?_ ?_
  · intro g hg
    rw [hW]
    exact mem_normalizer_iSup_oddCoreIn (mem_inf.mp hg).2
  · exact (oddCoreIn_le_of_isTwoComponentIn hK.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

@[expose] def Lemma39TwoDiscKPAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      (∃ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
        orderOf z = 2) →
      ¬ (IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)) ∧
          IsInvolutionCoreFree (coreQuot K' ⧸ center (coreQuot K'))) →
      ¬ (IsInvolutionCoreFreeInv (coreQuot K) ∧ IsInvolutionCoreFreeInv (coreQuot K')) →
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

theorem lemma39TwoDiscKCAt_of_KP (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) {R : SigOrientation}
    (h : Lemma39TwoDiscKPAt R) : Lemma39TwoDiscKCAt R := by
  intro G _ _ hG N hN hr K K' V B hP hR hW hz hnboth hZ' hhub hK'H hcase hdisc hconn
  by_cases hboth : IsInvolutionCoreFreeInv (coreQuot K) ∧ IsInvolutionCoreFreeInv (coreQuot K')
  · obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
    exact le_normalizer_wGroup_of_involutionCoreFreeInv_both hq hR1 hG hN hK hK' hne hboth.1
      hboth.2 hV hVK' hBQ hBV hB hB8 hE hEB hEK hBN
  · exact h G hG N hN hr K K' V B hP hR hW hz hnboth hboth hZ' hhub hK'H hcase hdisc hconn

end CFSG.ComponentClassification.Sol76.Sig
