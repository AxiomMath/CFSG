module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigCover
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolType
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigPump

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem le_of_perfect_of_le_sup {X B O : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hXB : X ≤ normalizer (B : Set G)) (hOB : O ≤ normalizer (B : Set G))
    (hO : Odd (Nat.card O)) (hle : X ≤ B ⊔ O) : X ≤ B := by
  classical
  have hXp : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
  set Z := (X ⊓ B).subgroupOf X with hZ
  have hZn : Z.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hZ, mem_subgroupOf] at ha ⊢
    refine ⟨(g * a * g⁻¹).2, ?_⟩
    simpa using (mem_normalizer_iff.mp (hXB g.2) a).mp ha.2
  have h1 := AS81.card_sup_mul_card_inf_of_le_normalizer_left hXB
  have h2 := AS81.card_sup_mul_card_inf_of_le_normalizer_left hOB
  have hZcard : Nat.card Z = Nat.card (X ⊓ B : Subgroup G) := by
    rw [hZ, ← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr inf_le_left]
  have hidx := Z.card_mul_index
  rw [hZcard] at hidx
  have hXBO : X ⊔ B ≤ O ⊔ B := sup_le (hle.trans (by rw [sup_comm])) le_sup_right
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hXBO
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hapos : 0 < Nat.card (X ⊓ B : Subgroup G) := Nat.card_pos
  have hwpos : 0 < Nat.card (O ⊓ B : Subgroup G) := Nat.card_pos
  have hu : Nat.card (X ⊔ B : Subgroup G) = Z.index * Nat.card B := by
    apply Nat.eq_of_mul_eq_mul_right hapos
    rw [h1, ← hidx]
    ring
  have hdvd : Z.index ∣ Nat.card O := by
    refine ⟨c * Nat.card (O ⊓ B : Subgroup G), ?_⟩
    apply Nat.eq_of_mul_eq_mul_right hBpos
    rw [← h2, hc, hu]
    ring
  have hodd : Odd (Nat.card (↥X ⧸ Z)) := Odd.of_dvd_nat hO hdvd
  have hsolv : Group.IsSolvable (↥X ⧸ Z) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect (↥X ⧸ Z) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective Z)
  have hsub : Subsingleton (↥X ⧸ Z) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable _ hsolv
  intro x hx
  have h3 : (QuotientGroup.mk (⟨x, hx⟩ : ↥X) : ↥X ⧸ Z) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, hZ, mem_subgroupOf] at h3
  exact h3.2

theorem eq_of_le_of_le_isTwoComponentIn {C J J' Y : Subgroup G} (hJ : IsTwoComponentIn J C)
    (hJ' : IsTwoComponentIn J' C) (hYJ : Y ≤ J) (hYJ' : Y ≤ J') (hY : ⁅Y, Y⁆ = Y)
    (hYinv : ∃ y ∈ Y, orderOf y = 2) : J = J' := by
  by_contra hne
  exact not_le_coreActionKernel_of_le hYJ hY hYinv
    (hYJ'.trans (GSThmB.B5a.le_coreActionKernel_of_ne hJ.1 hJ'.1 hJ.2 hJ'.2 hne))

theorem twoLayerIn_twoLayerIn (C : Subgroup G) : twoLayerIn (twoLayerIn C) = twoLayerIn C :=
  le_antisymm (map_subtype_le _) (twoLayerIn_le_of_forall fun _ hM =>
    le_twoLayerIn_of_isTwoComponentIn
      (isTwoComponentIn_of_le hM (le_twoLayerIn_of_isTwoComponentIn hM) (map_subtype_le _)))

theorem isTwoComponentIn_of_twoLayerIn {C J : Subgroup G}
    (hJ : IsTwoComponentIn J (twoLayerIn C)) : IsTwoComponentIn J C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC : twoLayerIn C ≤ C := map_subtype_le _
  have hn : ((twoLayerIn C).subgroupOf C).Normal := by
    have : (pLayer ↥C 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    rw [twoLayerIn, ← comap_subtype, comap_map_eq_self_of_injective C.subtype_injective]
    infer_instance
  exact ⟨hJ.1.trans hLC,
    GrSLit.isPComponent_subgroupOf_of_isSubnormal hJ.1 hLC hn.isSubnormal hJ.2⟩

theorem twoLayerIn_le_twoLayerIn_inf {H C : Subgroup G} (hLH : twoLayerIn C ≤ H) :
    twoLayerIn C ≤ twoLayerIn (H ⊓ C) :=
  twoLayerIn_le_of_forall fun _ hM =>
    le_twoLayerIn_of_isTwoComponentIn (isTwoComponentIn_of_le hM
      (le_inf ((le_twoLayerIn_of_isTwoComponentIn hM).trans hLH) hM.1) inf_le_right)

theorem twoLayerIn_centralizer_le {H : Subgroup G} {t : G} (htH : t ∈ H) {k : ℕ}
    (htk : orderOf t = 2 ^ k) (hLH : twoLayerIn (centralizer ({t} : Set G)) ≤ H) :
    twoLayerIn (centralizer ({t} : Set G)) ≤ twoLayerIn H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, htk])
  have h := GrSLit.pLayer_inf_centralizer_le (zpowers_le.mpr htH) hA2
  rw [centralizer_zpowers_eq] at h
  exact (twoLayerIn_le_twoLayerIn_inf hLH).trans h

theorem exists_pump_sup_eq (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {t : G} (htK' : t ∈ K')
    (ht2 : orderOf t = 2) :
    ∃ M ∈ pumpSet K (centralizer ({t} : Set G)),
      twoLayerIn (K ⊓ centralizer ({t} : Set G)) ⊔
          oddCoreIn (twoLayerIn (centralizer ({t} : Set G))) =
        M ⊔ oddCoreIn (twoLayerIn (centralizer ({t} : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  set Y := twoLayerIn (K ⊓ C) with hY
  have htQ : t ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm htK'
  obtain ⟨hY2, -, ⟨e⟩, h212, -⟩ := pump_facts hK htQ ht2
  obtain ⟨M, hM⟩ := pumpSet_nonempty hK htQ ht2
  have h1 : (pumpSet K C).ncard = 1 := by
    have hle : (pumpSet K C).ncard ≤ 1 := by
      by_contra h
      exact false_of_two_le_ncard_pumpSet hq (kStarKProper_of_simpleAmbient hG) hR1 hG
        (fun N' hN' => not_le_solomonKStarOf_top_of_simple hG hN') hN hK' hK hne.symm htK' ht2
        (by rw [← hC]; omega)
    have hpos : 0 < (pumpSet K C).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨M, hM⟩
    omega
  obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp h1
  have hMM' : M = M' := by
    have := hM
    rw [hM'] at this
    exact this
  subst hMM'
  refine ⟨M, hM, ?_⟩
  have hYL : Y ≤ twoLayerIn C := h212.trans (solomonKStarOf_le_twoLayerIn C)
  have hMt : IsTwoComponentIn M (twoLayerIn C) :=
    isTwoComponentIn_of_le hM.1.1 (le_twoLayerIn_of_isTwoComponentIn hM.1.1) (map_subtype_le _)
  have ht : Nat.card (↥M ⧸ Open.fusionZStar ↥M) = Nat.card (↥Y ⧸ Open.fusionZStar ↥Y) := by
    rw [card_fusionZStar_of_mem_pumpSet hK htQ ht2 hM, Nat.card_congr e.toEquiv]
  have hother : ∀ J : Subgroup G, IsTwoComponentIn J (twoLayerIn C) → J ≠ M →
      Y ≤ coreActionKernel J := by
    intro J hJ hJM
    have hJC := isTwoComponentIn_of_twoLayerIn hJ
    by_contra hYJ
    by_cases hJs : J ∈ solomonKStar G
    · have hJp : J ∈ pumpSet K C := ⟨⟨hJC, hJs⟩, hYJ⟩
      rw [hM'] at hJp
      exact hJM hJp
    · apply hYJ
      refine h212.trans (iSup₂_le fun J' hJ' => ?_)
      exact GSThmB.B5a.le_coreActionKernel_of_ne hJC.1 hJ'.1.1 hJC.2 hJ'.1.2
        fun h => hJs (h ▸ hJ'.2)
  have hYL' : Y ≤ twoLayerIn (twoLayerIn C) := by rw [twoLayerIn_twoLayerIn]; exact hYL
  exact sup_oddCoreIn_eq_of_moves_only hMt hYL'
    (UnbalancedCorr.commutator_eq_of_isPComponent hY2.1 hY2.2)
    (isQuasisimple_quotient_of_isPComponent hY2.1 hY2.2) hM.2 ht hother

variable {H : Subgroup G}

theorem le_twoLayerIn_of_le (hN : IsSolomonChoice N)
    (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    {K : Subgroup G} (hK : K ∈ kStarComponents N) : K ≤ twoLayerIn H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', hK', hne⟩ := exists_mem_kStarComponents_ne hN K
  obtain ⟨t, htK', ht2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK'.2
  have htQ : t ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne htK'
  obtain ⟨-, hsup, -, h212, -⟩ := pump_facts hK htQ ht2
  have hYL : twoLayerIn (K ⊓ centralizer ({t} : Set G)) ≤ twoLayerIn H :=
    (h212.trans (solomonKStarOf_le_twoLayerIn _)).trans
      (twoLayerIn_centralizer_le (hKH K' hK' htK') (k := 1) (by rw [pow_one]; exact ht2)
        (hLH K' hK' t htK' ht2))
  have hKN : K ≤ normalizer (twoLayerIn H : Set G) :=
    (hKH K hK).trans (le_normalizer_twoLayerIn H)
  exact le_of_perfect_of_le_sup (UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2)
    hKN ((map_subtype_le _).trans hKN) (Nat.coprime_two_left.mp (coprime_card_oddCoreIn K))
    (hsup.symm.le.trans (sup_le_sup_right hYL _))

theorem exists_pump_le (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    {K K' : Subgroup G} (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {t : G} (htK' : t ∈ K') (ht2 : orderOf t = 2) :
    ∃ M ∈ pumpSet K (centralizer ({t} : Set G)), ∃ B : Subgroup G, IsTwoComponentIn B H ∧
      M ≤ B ∧ K ≤ B ∧ IsTwoComponentIn M (H ⊓ centralizer ({t} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  have htQ : t ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm htK'
  obtain ⟨hY2, hsup, -, -, -⟩ := pump_facts hK htQ ht2
  obtain ⟨M, hM, hPsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK hK' hne htK' ht2
  have htH : t ∈ H := hKH K' hK' htK'
  have hLtH : twoLayerIn C ≤ H := hLH K' hK' t htK' ht2
  have hLtL : twoLayerIn C ≤ twoLayerIn H :=
    twoLayerIn_centralizer_le htH (k := 1) (by rw [pow_one]; exact ht2) hLtH
  have hMH : M ≤ H := (le_twoLayerIn_of_isTwoComponentIn hM.1.1).trans hLtH
  have hMHC : IsTwoComponentIn M (H ⊓ C) :=
    isTwoComponentIn_of_le hM.1.1 (le_inf hMH hM.1.1.1) inf_le_right
  obtain ⟨B, hBH, hBpc, hMB, -⟩ := foote_lemma_2_1_iv_subgroup htH ht2 hMHC.1 hMHC.2
  have hLHB : twoLayerIn H ≤ normalizer (B : Set G) := twoLayerIn_le_normalizer hBH hBpc
  have hK'L := le_twoLayerIn_of_le hN hKH hLH hK'
  have hKL := le_twoLayerIn_of_le hN hKH hLH hK
  have htB : conjugate B t = B := mem_normalizer_iff_map_conj_eq.mp (inv_mem (hLHB (hK'L htK')))
  rw [htB, sup_idem] at hMB
  have hYB : twoLayerIn (K ⊓ C) ≤ B := by
    refine le_of_perfect_of_le_sup (UnbalancedCorr.commutator_eq_of_isPComponent hY2.1 hY2.2)
      (((hY2.1.trans inf_le_left).trans hKL).trans hLHB)
      (((map_subtype_le _).trans hLtL).trans hLHB)
      (Nat.coprime_two_left.mp (coprime_card_oddCoreIn _)) ?_
    calc twoLayerIn (K ⊓ C) ≤ twoLayerIn (K ⊓ C) ⊔ oddCoreIn (twoLayerIn C) := le_sup_left
      _ = M ⊔ oddCoreIn (twoLayerIn C) := hPsup
      _ ≤ B ⊔ oddCoreIn (twoLayerIn C) := sup_le_sup_right hMB _
  refine ⟨M, hM, B, ⟨hBH, hBpc⟩, hMB, ?_, hMHC⟩
  exact le_of_perfect_of_le_sup (UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2)
    (hKL.trans hLHB) (((map_subtype_le _).trans hKL).trans hLHB)
    (Nat.coprime_two_left.mp (coprime_card_oddCoreIn K))
    (hsup.symm.le.trans (sup_le_sup_right hYB _))

theorem exists_isTwoComponentIn_le (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    {K : Subgroup G} (hK : K ∈ kStarComponents N) :
    ∃ B : Subgroup G, IsTwoComponentIn B H ∧ K ≤ B := by
  obtain ⟨K', hK', hne⟩ := exists_mem_kStarComponents_ne hN K
  obtain ⟨t, htK', ht2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK'.2
  obtain ⟨-, -, B, hB, -, hKB, -⟩ := exists_pump_le hq hR1 hG hN hKH hLH hK hK' hne.symm htK' ht2
  exact ⟨B, hB, hKB⟩

theorem cover_of_ne (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    {K K' B B' : Subgroup G} (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hB : IsTwoComponentIn B H) (hB' : IsTwoComponentIn B' H) (hKB : K ≤ B) (hK'B' : K' ≤ B')
    (hBB' : B ≠ B') : K ⊔ oddCoreIn B = B ∧ B ∈ solomonKStar G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKperf := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  have hKinv := exists_orderOf_eq_two_of_mem_solomonKStar hK.2
  have hne : K ≠ K' := by
    rintro rfl
    exact hBB' (eq_of_le_of_le_isTwoComponentIn hB hB' hKB hK'B' hKperf hKinv)
  obtain ⟨s, hsK', hs2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK'.2
  set C := centralizer ({s} : Set G) with hC
  have hsB : s ∈ coreActionKernel B :=
    GSThmB.B5a.le_coreActionKernel_of_ne hB.1 hB'.1 hB.2 hB'.2 hBB' (hK'B' hsK')
  obtain ⟨M, hM, B'', hB'', hMB'', hKB'', hMHC⟩ :=
    exists_pump_le hq hR1 hG hN hKH hLH hK hK' hne hsK' hs2
  have hBB'' : B'' = B := eq_of_le_of_le_isTwoComponentIn hB'' hB hKB'' hKB hKperf hKinv
  subst hBB''
  have hs2' : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
  have hcov := inf_centralizer_sup_oddCoreIn_eq hs2' (zpowers_le.mpr hsB)
  rw [centralizer_zpowers_eq] at hcov
  have hBq : IsQuasisimple (↥B'' ⧸ pPrimeCore 2 ↥B'') :=
    isQuasisimple_quotient_of_isPComponent hB.1 hB.2
  obtain ⟨hJ2, hJL, hJsup, ⟨eJ⟩⟩ := cover_facts hBq inf_le_left hcov
  have hMY : IsTwoComponentIn M (B'' ⊓ C) :=
    isTwoComponentIn_of_le hMHC (le_inf hMB'' (hMHC.1.trans inf_le_right))
      (inf_le_inf_right _ hB.1)
  have hMJ : M = oddResidualIn (B'' ⊓ C) := by
    have hMle : M ≤ oddResidualIn (B'' ⊓ C) := hJL ▸ le_twoLayerIn_of_isTwoComponentIn hMY
    exact eq_of_le_of_le_isTwoComponentIn hMY hJ2 le_rfl hMle
      (UnbalancedCorr.commutator_eq_of_isPComponent hMY.1 hMY.2)
      (exists_orderOf_eq_two_of_mem_solomonKStar hM.1.2)
  rw [← hMJ] at hJsup eJ
  have hsQ : s ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm hsK'
  have ht : Nat.card (↥B'' ⧸ Open.fusionZStar ↥B'') = Nat.card (↥K ⧸ Open.fusionZStar ↥K) := by
    rw [← card_fusionZStar_of_mem_pumpSet hK hsQ hs2 hM]
    exact (Nat.card_congr (Sol78.fusionZStarQuotOfCore eJ).toEquiv).symm
  have hBB : IsTwoComponentIn B'' B'' := isTwoComponentIn_of_le hB le_rfl hB.1
  have hother : ∀ J : Subgroup G, IsTwoComponentIn J B'' → J ≠ B'' → K ≤ coreActionKernel J :=
    fun J hJ hJB => (hJB (Foote5.SolMax.eq_of_le_of_isTwoComponentIn hJ hBB hJ.1)).elim
  have h := sup_oddCoreIn_eq_of_moves_only hBB
    (hKB.trans (le_twoLayerIn_of_isTwoComponentIn hBB)) hKperf
    (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2)
    (not_le_coreActionKernel_of_le hKB hKperf hKinv) ht hother
  refine ⟨h.trans (sup_eq_left.mpr (map_subtype_le _)), ?_⟩
  have hYdef : twoLayerIn (B'' ⊓ C) = M := hJL.trans hMJ.symm
  have hMn : B'' ⊓ C ≤ normalizer (M : Set G) := hYdef ▸ le_normalizer_twoLayerIn (B'' ⊓ C)
  have hOCM : oddCoreIn C ≤ normalizer (M : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hM.1.1.1 hM.1.1.2
  have hres : oddResidualIn (oddCoreIn C ⊔ (B'' ⊓ C)) = M := by
    apply le_antisymm
    · set W := oddCoreIn C ⊔ (oddCoreIn B'' ⊓ C) with hW
      have hWM : W ≤ normalizer (M : Set G) :=
        sup_le hOCM ((inf_le_inf_right _ (map_subtype_le _)).trans hMn)
      have hWodd : Odd (Nat.card W) := odd_card_sup_of_le_normalizer
        (inf_le_right.trans (le_normalizer_oddCoreIn C))
        (Nat.coprime_two_left.mp (coprime_card_oddCoreIn C))
        (Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
          (Subgroup.card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn B'')))
      have hYle : B'' ⊓ C ≤ M ⊔ W := by
        intro y hy
        have hyB : y ∈ oddCoreIn B'' ⊔ M := by rw [sup_comm, hJsup]; exact hy.1
        obtain ⟨o, ho, m, hm, rfl⟩ := exists_mul_of_mem_sup_normalizer
          (hMB''.trans (le_normalizer_oddCoreIn B'')) hyB
        have hmC : m ∈ C := (hMY.1 hm).2
        have hoC : o ∈ C := by
          have e : o = o * m * m⁻¹ := by group
          rw [e]
          exact mul_mem hy.2 (inv_mem hmC)
        exact mul_mem (mem_sup_right (mem_sup_right ⟨ho, hoC⟩)) (mem_sup_left hm)
      have hle : oddCoreIn C ⊔ (B'' ⊓ C) ≤ M ⊔ W := sup_le (le_sup_left.trans le_sup_right) hYle
      rw [oddResidualIn, closure_le]
      rintro g ⟨hg, k, hk⟩
      exact mem_of_mem_sup_of_coprime_index hWM (Nat.Coprime.coprime_dvd_right
        (Subgroup.index_dvd_card _) (Nat.coprime_two_left.mpr hWodd)) (hle hg) hk
    · calc M = oddResidualIn (B'' ⊓ C) := hMJ
        _ ≤ oddResidualIn (oddCoreIn C ⊔ (B'' ⊓ C)) :=
          closure_mono fun g hg => ⟨mem_sup_right hg.1, hg.2⟩
  have hCU : centralizer ((zpowers s : Subgroup G) : Set G) = C := centralizer_zpowers_eq s
  have hmemB : IsSolomonMember B'' := by
    refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hB.1 hB.2, zpowers s,
      zpowers_ne_bot_of_orderOf_eq_two hs2, hs2', zpowers_le.mpr hsB, ?_⟩
    rw [hCU, hres]
    exact hM.1.1
  have hmemM : IsSolomonMember M := hM.1.2.1.1
  have hlt : SolomonLt B'' M := by
    refine ⟨hmemB, hmemM, zpowers s, hs2', zpowers_le.mpr hsB, ?_⟩
    rw [hCU, hYdef]
    have hcl : conjClosure M (twoLayerIn C) = M :=
      le_antisymm (Sol78.conjClosure_le le_rfl (twoLayerIn_le_normalizer hM.1.1.1 hM.1.1.2))
        (le_conjClosure M _)
    rw [hcl]
    exact isTwoComponentIn_of_le hM.1.1 le_rfl hM.1.1.1
  exact mem_solomonKStar_of_solomonEquiv hM.1.2
    ⟨hmemM, Relation.ReflTransGen.single ⟨⟨Sol78.fusionZStarQuotOfCore eJ⟩, Or.inr hlt⟩⟩

theorem cover_or_single (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H) :
    (∀ K ∈ kStarComponents N, ∃ B ∈ kStarComponents H, K ≤ B ∧ K ⊔ oddCoreIn B = B) ∨
    ∃ B : Subgroup G, IsTwoComponentIn B H ∧ ∀ K ∈ kStarComponents N, K ≤ B := by
  classical
  choose! f hf using fun K (hK : K ∈ kStarComponents N) =>
    exists_isTwoComponentIn_le hq hR1 hG hN hKH hLH hK
  by_cases hall : ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, f K = f K'
  · right
    obtain ⟨K₀, hK₀, -⟩ := exists_mem_kStarComponents_ne hN ⊥
    exact ⟨f K₀, (hf K₀ hK₀).1, fun K hK => (hall K hK K₀ hK₀) ▸ (hf K hK).2⟩
  · left
    push Not at hall
    obtain ⟨K₀, hK₀, K₁, hK₁, h01⟩ := hall
    intro K hK
    obtain ⟨K', hK', hKK'⟩ : ∃ K' ∈ kStarComponents N, f K ≠ f K' := by
      by_cases h0 : f K = f K₀
      · exact ⟨K₁, hK₁, h0 ▸ h01⟩
      · exact ⟨K₀, hK₀, h0⟩
    obtain ⟨h1, h2⟩ := cover_of_ne hq hR1 hG hN hKH hLH hK hK' (hf K hK).1 (hf K' hK').1
      (hf K hK).2 (hf K' hK').2 hKK'
    exact ⟨f K, ⟨(hf K hK).1, h2⟩, (hf K hK).2, h1⟩

theorem exists_isTwoComponentIn_forall_le (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N) (hKH : ∀ K ∈ kStarComponents N, K ≤ H)
    (hLH : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      twoLayerIn (centralizer ({s} : Set G)) ≤ H)
    (hcent : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ H) :
    ∃ B : Subgroup G, IsTwoComponentIn B H ∧ ∀ K ∈ kStarComponents N, K ≤ B := by
  rcases cover_or_single hq hR1 hG hN hKH hLH with hcov | h
  · exact (false_of_cover hq hF hG hN hcov hcent).elim
  · exact h

end CFSG.ComponentClassification.Sol76.Sig
