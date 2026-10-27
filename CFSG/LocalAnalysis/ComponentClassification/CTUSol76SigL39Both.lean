module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39Bal
public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem iSup_oddCoreIn_eq_of_involutionCoreFree (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)))
    (hfree' : IsInvolutionCoreFree (coreQuot K' ⧸ center (coreQuot K')))
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
    refine (oddCoreIn_inf_le_of_involutionCoreFree hq hR1 hG hN hK hK' hne hfree (hVK' hv) hv2 hV
      hVK' hVv (hEK he) he2 (hcomm e he v hv)).trans ?_
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
    refine (oddCoreIn_inf_le_of_involutionCoreFree hq hR1 hG hN hK' hK hne.symm hfree' (hEK he) he2
      hE hEK hEe' (hVK' hv) hv2 (hcomm e he v hv).symm).trans ?_
    exact le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)

omit [Finite G] in
theorem mem_normalizer_iSup_oddCoreIn {V : Subgroup G} {g : G}
    (hg : g ∈ centralizer (V : Set G)) :
    g ∈ normalizer ((⨆ (v : G) (_ : v ∈ V) (_ : v ≠ 1),
      oddCoreIn (centralizer ({v} : Set G)) : Subgroup G) : Set G) := by
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun v => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun hv => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun _ => ?_
  have hgv : g ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hg) v hv).symm
  exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer_oddCoreIn _ hgv)

theorem le_normalizer_wGroup_of_involutionCoreFree_both (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') (hfree : IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)))
    (hfree' : IsInvolutionCoreFree (coreQuot K' ⧸ center (coreQuot K')))
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
    rw [← hWE, wGroup_eq_iSup_of_involutionCoreFree hq hR1 hG hN hK hK' hne hfree hE hEK hV hVK'
      hEV, iSup_oddCoreIn_eq_of_involutionCoreFree hq hR1 hG hN hK hK' hne hfree hfree' hE hEK hV
      hVK' hEV]
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

@[expose] def Lemma39TwoDiscKBAt (R : SigOrientation) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → R G N K K' → wGroup B V ≠ ⊥ →
      ¬ (IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)) ∧
          IsInvolutionCoreFree (coreQuot K' ⧸ center (coreQuot K'))) →
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

theorem lemma39TwoDiscKKAt_of_KB (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) {R : SigOrientation}
    (h : Lemma39TwoDiscKBAt R) : Lemma39TwoDiscKKAt R := by
  intro G _ _ hG N hN hr K K' V B hP hR hW hK'H hcase hdisc hconn
  by_cases hboth : IsInvolutionCoreFree (coreQuot K ⧸ center (coreQuot K)) ∧
      IsInvolutionCoreFree (coreQuot K' ⧸ center (coreQuot K'))
  · obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
    exact le_normalizer_wGroup_of_involutionCoreFree_both hq hR1 hG hN hK hK' hne hboth.1 hboth.2
      hV hVK' hBQ hBV hB hB8 hE hEB hEK hBN
  · exact h G hG N hN hr K K' V B hP hR hW hboth hK'H hcase hdisc hconn

end CFSG.ComponentClassification.Sol76.Sig
