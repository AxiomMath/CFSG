module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39VHub
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvBender
public import CFSG.Goldschmidt.Steps.LemmaXBasic

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem nonempty_fusionZStar_equiv_of_mem_pumpSet (hK : K ∈ kStarComponents N) {b : G}
    (hbQ : b ∈ coreActionKernel K) (hb2 : orderOf b = 2) {M : Subgroup G}
    (hM : M ∈ pumpSet K (centralizer ({b} : Set G))) :
    Nonempty (↥K ⧸ Open.fusionZStar ↥K ≃* ↥M ⧸ Open.fusionZStar ↥M) := by
  classical
  set C := centralizer ({b} : Set G) with hC
  have hCzb : centralizer ((zpowers b : Subgroup G) : Set G) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hUQ : zpowers b ≤ coreActionKernel K := zpowers_le.mpr hbQ
  obtain ⟨-, -, -, h212, -⟩ := pump_facts hK hbQ hb2
  have hYL : twoLayerIn (K ⊓ C) ≤ twoLayerIn C := h212.trans (solomonKStarOf_le_twoLayerIn C)
  have hlt : SolomonLt K M := by
    refine ⟨hK.2.1.1, hM.1.2.1.1, zpowers b, hU2, hUQ, ?_⟩
    rw [hCzb]
    exact isTwoComponentIn_conjClosure_of_not_le hM.1.1 hYL hM.2
  have heq : SolomonEquiv K M :=
    hK.2.1.2 K M ⟨hK.2.1.1, Relation.ReflTransGen.refl⟩ hlt
  exact nonempty_fusionZStar_equiv_of_reflTransGen heq.2

theorem oddCoreIn_inf_le_of_involutionCoreFree (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)))
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
  obtain ⟨e1⟩ := GrSLit.nonempty_image_center_quotient_equiv hMC.1 hMC.2
  obtain ⟨e2⟩ := nonempty_fusionZStar_equiv_of_mem_pumpSet hK hvQ hv2 hM
  obtain ⟨e3⟩ := FooteLit.nonempty_fusionZStar_quotient_equiv ↥K
  have hfreeM := isInvolutionCoreFree_of_mulEquiv ((e3.symm.trans e2).trans e1.symm) hfree
  have hkey : ⁅M, X⁆ ≤ oddCoreIn Cv :=
    commutator_le_oddCoreIn_of_involutionCoreFree hMC.1 hMC.2 hfreeM heM
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

theorem theta_eq_oddCoreIn_of_involutionCoreFree (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)))
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
  have hcrux := oddCoreIn_inf_le_of_involutionCoreFree hq hR1 hG hN hK hK' hne hfree (hV₁K' hv)
    hv2 hV₁ hV₁K' hV₁v heK he2 hve
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

theorem wGroup_eq_iSup_of_involutionCoreFree (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)))
    {E V₁ : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) (hV₁ : IsKleinFour V₁)
    (hV₁K' : V₁ ≤ K') (hEV₁ : E ≤ centralizer (V₁ : Set G)) :
    wGroup E V₁ = ⨆ (e : G) (_ : e ∈ E) (_ : e ≠ 1), oddCoreIn (centralizer ({e} : Set G)) := by
  refine iSup_congr fun e => iSup_congr fun he => iSup_congr fun he1 => ?_
  have hV₁e : V₁ ≤ centralizer ({e} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV₁ he)) w hw)
  exact theta_eq_oddCoreIn_of_involutionCoreFree hq hR1 hG hN hK hK' hne hfree hV₁ hV₁K' (hEK he)
    (orderOf_eq_two_of_isKleinFour hE he he1) hV₁e

theorem le_normalizer_wGroup_of_involutionCoreFree (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)))
    {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N) :
    K' ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hE2 : IsPGroup 2 E := isPGroup_of_isKleinFour hE
  have hEQ : E ≤ coreActionKernel K' := hEK.trans (le_coreActionKernel_of_ne hK' hK hne.symm)
  have hW0 := wGroup_eq_iSup_of_involutionCoreFree hq hR1 hG hN hK hK' hne hfree hE hEK hV hVK'
    hEV
  rw [← inf_centralizer_sup_oddCoreIn_eq hE2 hEQ]
  refine sup_le ?_ ?_
  · intro g hg
    have hgK' : g ∈ K' := (mem_inf.mp hg).1
    have hgE : g ∈ centralizer (E : Set G) := (mem_inf.mp hg).2
    have hEg : E.map (MulAut.conj g).toMonoidHom = E := map_conj_eq_of_mem_centralizer hgE
    set V' := V.map (MulAut.conj g).toMonoidHom with hV'def
    have hV' : IsKleinFour V' := isKleinFour_map_conj hV g
    have hV'K' : V' ≤ K' := by
      rintro _ ⟨w, hw, rfl⟩
      exact mul_mem (mul_mem hgK' (hVK' hw)) (inv_mem hgK')
    have hEV' : E ≤ centralizer (V' : Set G) := by
      rw [← hEg]
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hxw : w * x = x * w := (mem_centralizer_iff.mp (hEV hx)) w hw
      calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
        _ = g * (x * w) * g⁻¹ := by rw [hxw]
        _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
    have hW1 := wGroup_eq_iSup_of_involutionCoreFree hq hR1 hG hN hK hK' hne hfree hE hEK hV'
      hV'K' hEV'
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [← hWE, map_wGroup, hEg, hW1, ← hW0]
    exact mem_normalizer_iff_map_conj_eq.mpr key
  · exact (oddCoreIn_le_of_isTwoComponentIn hK'.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

theorem hasStronglyEmbedded_of_coreQuot {K : Subgroup G}
    (h : ∃ M : Subgroup (coreQuot K), Assembly.Dichotomy.dichotomyStronglyEmbedded M) :
    HasStronglyEmbedded ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM⟩ := h
  have hodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact ⟨M.comap (QuotientGroup.mk' (pPrimeCore 2 ↥K)),
    Goldschmidt.LemmaX.fusionStronglyEmbedded_comap _ (QuotientGroup.mk'_surjective _) hodd hM⟩

@[expose] def InvolutionCoreFreeJLA : Prop :=
  ∀ (L : Type) [Group L] [Finite L],
    (Nonempty (L ≃* ↥CFSG.Open.properTwoGenCoreJ1) ∨
        CFSG.Open.StatedClassicalModel L .PSL 3 2 2 ∨
        Nonempty (L ≃* alternatingGroup (Fin 9))) →
      IsInvolutionCoreFree L

theorem isInvolutionCoreFree_of_isSolomonI
    (hJLA : InvolutionCoreFreeJLA) {Q : Type} [Group Q] [Finite Q] (hQ : IsSolomonI Q) :
    IsInvolutionCoreFree (Q ⧸ center Q) := by
  rcases hQ with hJ | hL | hB | ⟨hA, -⟩
  · exact hJLA _ (Or.inl hJ)
  · exact hJLA _ (Or.inr (Or.inl hL))
  · exact isInvolutionCoreFree_of_isBenderGroup hB
  · exact hJLA _ (Or.inr (Or.inr hA))

@[expose] def Lemma39TwoDiscKKAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      K' ≤ normalizer (wGroup B V : Set G) →
        ((IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K)) ∨
            CFSG.Open.pRank 2 K ≤ 2) →
        (center (coreQuot K) ≠ ⊥ ∨ ¬ (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected ∨
          ∀ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
            orderOf z ≠ 2) →
        (∀ U E : Subgroup G, IsKleinFour U → U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E →
          E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (U : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)

section Certified

theorem isSolomonI_of_not_threeB (hBig : QuasisimpleBigCenterRankThree)
    (hSJ : QuasisimpleSylowFourJoinedSCN) (hG : SimpleAmbient G) (hN : IsSolomonChoice N)
    (hr : (kStarComponents N).ncard = 2) (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K')
    (h3b : ∀ z ∈ (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel (solomonKStarOf N),
      orderOf z ≠ 2)
    (hSE : ∃ M : Subgroup (coreQuot K'), Assembly.Dichotomy.dichotomyStronglyEmbedded M) :
    IsSolomonI (coreQuot K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases exists_involution_or_three_le_of_ncard_eq_two hN hr hK hK' hne with
    ⟨z, hz, hz2⟩ | ⟨h3K, -, hdisc⟩
  · exact absurd hz2 (h3b z hz)
  obtain ⟨hdK, -⟩ := hdisc (Or.inr (hasStronglyEmbedded_of_coreQuot hSE))
  have hdQ : IsTwoDisconnected (coreQuot K) := by
    by_contra hc
    obtain ⟨E, F, hE, hF, hEF⟩ := hdK
    have h3top : 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥K) := by
      rw [← SectionRank.pRank_eq_open_pRank_top, pRank_coe_eq]
      exact h3K
    obtain ⟨A, -, hA, hA8⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) h3top
    have hodd : Odd (Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥K)).ker) := by
      rw [QuotientGroup.ker_mk']
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hEF (reflTransGen_of_twoConnected_quot (QuotientGroup.mk' (pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective _) hodd hc hA (by rw [hA8]; norm_num) hE hF)
  by_contra hI
  exact not_isTwoDisconnected_coreQuot_of_not_isSolomonI hBig hSJ hG hK h3K hI hdQ

theorem lemma39TwoDiscKAt_of_KK (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hBig : QuasisimpleBigCenterRankThree)
    (hSJ : QuasisimpleSylowFourJoinedSCN) (hJLA : InvolutionCoreFreeJLA) {R : SigOrientation}
    (h : Lemma39TwoDiscKKAt R) : Lemma39TwoDiscKAt R := by
  intro G _ _ hG N hN hr K K' V B hP hR hW
  refine ⟨h G hG N hN hr K K' V B hP hR hW, fun hSE _ h3b => ?_⟩
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  have hI := isSolomonI_of_not_threeB hBig hSJ hG hN hr hK hK' hne h3b hSE
  exact le_normalizer_wGroup_of_involutionCoreFree hq hR1 hG hN hK hK' hne
    (isInvolutionCoreFree_of_isSolomonI hJLA hI) hV hVK' hBQ hBV hB hB8 hE hEB hEK hBN

end Certified

end CFSG.ComponentClassification.Sol76.Sig
