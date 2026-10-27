module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Pump
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Tools
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Rank

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

@[expose] def pumpSet (K' C : Subgroup G) : Set (Subgroup G) :=
  {M | M ∈ kStarComponents C ∧ ¬ twoLayerIn (K' ⊓ C) ≤ coreActionKernel M}

theorem mem_coreActionKernel_of_ne {N K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hKK' : K ≠ K') {b : G} (hbK : b ∈ K) :
    b ∈ coreActionKernel K' :=
  GSThmB.B5a.le_coreActionKernel_of_ne hK'.1.1 hK.1.1 hK'.1.2 hK.1.2 (Ne.symm hKK') hbK

theorem pump_facts {N K' : Subgroup G} (hK' : K' ∈ kStarComponents N) {b : G}
    (hbQ : b ∈ coreActionKernel K') (hb2 : orderOf b = 2) :
      IsTwoComponentIn (twoLayerIn (K' ⊓ centralizer ({b} : Set G)))
        (K' ⊓ centralizer ({b} : Set G)) ∧
      twoLayerIn (K' ⊓ centralizer ({b} : Set G)) ⊔ oddCoreIn K' = K' ∧
      Nonempty (↥(twoLayerIn (K' ⊓ centralizer ({b} : Set G))) ⧸
          Open.fusionZStar ↥(twoLayerIn (K' ⊓ centralizer ({b} : Set G))) ≃*
        ↥K' ⧸ Open.fusionZStar ↥K') ∧
      twoLayerIn (K' ⊓ centralizer ({b} : Set G)) ≤ solomonKStarOf (centralizer ({b} : Set G)) ∧
      2 ≤ CFSG.Open.pRank 2 (twoLayerIn (K' ⊓ centralizer ({b} : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({b} : Set G) with hC
  have hCzb : centralizer ((zpowers b : Subgroup G) : Set G) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hbne : zpowers b ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hb2
    norm_num at hb2
  have hUQ : zpowers b ≤ coreActionKernel K' := zpowers_le.mpr hbQ
  have hK'q : IsQuasisimple (↥K' ⧸ pPrimeCore 2 ↥K') :=
    isQuasisimple_quotient_of_isPComponent hK'.1.1 hK'.1.2
  have hcov := inf_centralizer_sup_oddCoreIn_eq hU2 hUQ
  rw [hCzb] at hcov
  obtain ⟨hY2, hYL, hYsup, ⟨eY⟩⟩ := cover_facts hK'q inf_le_left hcov
  have h212 := lemma212Input G K' (zpowers b) hK'.2 hbne hU2 hUQ
  rw [hCzb] at h212
  refine ⟨hYL ▸ hY2, hYL ▸ hYsup, ⟨?_⟩, h212, ?_⟩
  · rw [hYL]
    exact Sol78.fusionZStarQuotOfCore eY
  · rw [hYL]
    exact (two_le_pRank_of_mem_solomonKStar hK'.2).trans
      (pRank_le_of_sup_oddCoreIn (hY2.1.trans inf_le_left) hYsup)

theorem card_fusionZStar_of_mem_pumpSet {N K' : Subgroup G} (hK' : K' ∈ kStarComponents N)
    {b : G} (hbQ : b ∈ coreActionKernel K') (hb2 : orderOf b = 2) {M : Subgroup G}
    (hM : M ∈ pumpSet K' (centralizer ({b} : Set G))) :
    Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥K' ⧸ Open.fusionZStar ↥K') := by
  classical
  set C := centralizer ({b} : Set G) with hC
  have hCzb : centralizer ((zpowers b : Subgroup G) : Set G) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hUQ : zpowers b ≤ coreActionKernel K' := zpowers_le.mpr hbQ
  obtain ⟨-, -, -, h212, -⟩ := pump_facts hK' hbQ hb2
  have hYL : twoLayerIn (K' ⊓ C) ≤ twoLayerIn C := h212.trans (solomonKStarOf_le_twoLayerIn C)
  have hlt : SolomonLt K' M := by
    refine ⟨hK'.2.1.1, hM.1.2.1.1, zpowers b, hU2, hUQ, ?_⟩
    rw [hCzb]
    exact isTwoComponentIn_conjClosure_of_not_le hM.1.1 hYL hM.2
  have heq : SolomonEquiv K' M :=
    hK'.2.1.2 K' M ⟨hK'.2.1.1, Relation.ReflTransGen.refl⟩ hlt
  obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen heq.2
  exact (Nat.card_congr e.toEquiv).symm

theorem pumpSet_nonempty {N K' : Subgroup G} (hK' : K' ∈ kStarComponents N) {b : G}
    (hbQ : b ∈ coreActionKernel K') (hb2 : orderOf b = 2) :
    (pumpSet K' (centralizer ({b} : Set G))).Nonempty := by
  classical
  set C := centralizer ({b} : Set G) with hC
  obtain ⟨hY2, -, -, h212, hYr⟩ := pump_facts hK' hbQ hb2
  set Y := twoLayerIn (K' ⊓ C) with hY
  have hYperf : ⁅Y, Y⁆ = Y := UnbalancedCorr.commutator_eq_of_isPComponent hY2.1 hY2.2
  have hYinv : ∃ x ∈ Y, orderOf x = 2 :=
    exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hYr)
  obtain ⟨M, hM, hYM⟩ := exists_not_le_coreActionKernel_of_le_twoLayerIn hYperf
    (h212.trans (solomonKStarOf_le_twoLayerIn C)) hYinv
  refine ⟨M, ⟨hM, ?_⟩, hYM⟩
  by_contra hMs
  apply hYM
  refine h212.trans (iSup₂_le fun J hJ => ?_)
  exact GSThmB.B5a.le_coreActionKernel_of_ne hM.1 hJ.1.1 hM.2 hJ.1.2
    fun h => hMs (h ▸ hJ.2)

theorem pumpSet_disjoint {N K' K'' : Subgroup G} (hK' : K' ∈ kStarComponents N)
    (hK'' : K'' ∈ kStarComponents N) (hne : K' ≠ K'') {b : G} (hb' : b ∈ coreActionKernel K')
    (hb'' : b ∈ coreActionKernel K'') (hb2 : orderOf b = 2) :
    Disjoint (pumpSet K' (centralizer ({b} : Set G)))
      (pumpSet K'' (centralizer ({b} : Set G))) := by
  classical
  set C := centralizer ({b} : Set G) with hC
  rw [Set.disjoint_left]
  intro M hM' hM''
  obtain ⟨hY'2, -, ⟨e'⟩, h212', -⟩ := pump_facts hK' hb' hb2
  obtain ⟨hY''2, -, -, h212'', -⟩ := pump_facts hK'' hb'' hb2
  set Y' := twoLayerIn (K' ⊓ C) with hY'
  set Y'' := twoLayerIn (K'' ⊓ C) with hY''
  have hodd : ¬ 2 ∣ Nat.card ↥⁅Y', Y''⁆ := by
    have hle : ⁅Y', Y''⁆ ≤ oddCoreIn N :=
      (commutator_mono (hY'2.1.trans inf_le_left) (hY''2.1.trans inf_le_left)).trans
        (FooteLit.commutator_le_oddCoreIn_of_ne hK'.1 hK''.1 hne)
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_oddCoreIn N)
      (h.trans (card_dvd_of_le hle))
  have ht' : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥Y' ⧸ Open.fusionZStar ↥Y') := by
    rw [card_fusionZStar_of_mem_pumpSet hK' hb' hb2 hM', Nat.card_congr e'.toEquiv]
  have hY''L : Y'' ≤ twoLayerIn C := h212''.trans (solomonKStarOf_le_twoLayerIn C)
  have hodd' : ¬ 2 ∣ Nat.card ↥⁅Y'', Y'⁆ := by rwa [commutator_comm]
  exact hM''.2 (le_coreActionKernel_of_odd_commutator hM'.1.1
    (h212'.trans (solomonKStarOf_le_twoLayerIn C))
    (UnbalancedCorr.commutator_eq_of_isPComponent hY'2.1 hY'2.2)
    (isQuasisimple_quotient_of_isPComponent hY'2.1 hY'2.2) hM'.2 ht'
    (hY''L.trans (map_subtype_le _))
    (hY''L.trans (FooteLit.twoLayerIn_le_normalizer hM'.1.1.1 hM'.1.1.2)) hodd')

end CFSG.ComponentClassification.Sol76T13
