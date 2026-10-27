module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Tools

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

theorem kStarComponents_normalizer_eq (hbal : Lemma316BalancedInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) :
    kStarComponents (normalizer (solomonKStarOf N : Set G)) = kStarComponents N := by
  obtain ⟨K, hK, -⟩ := exists_mem_kStarComponents_ne hN ⊥
  have hne : (kStarComponents N).Nonempty := ⟨K, hK⟩
  have heq := hbal G hG N hN _ le_rfl hne
  rwa [← solomonKStarOf_eq_sSup] at heq

theorem mem_kStarComponents_of_steps (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜) (hG : 𝒜 G)
    {N : Subgroup G} (hN : IsSolomonChoice N) {K : Subgroup G} (hK : K ∈ kStarComponents N)
    {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (centralizer ({b} : Set G))) (hJs : J ∈ solomonKStar G)
    (hJH : J ≤ twoLayerIn (normalizer (solomonKStarOf N : Set G))) : J ∈ kStarComponents N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hJN
  set D := solomonKStarOf N with hD
  set H := normalizer (D : Set G) with hH
  set Cb := centralizer ({b} : Set G) with hCb
  have hHcomp : kStarComponents H = kStarComponents N :=
    kStarComponents_normalizer_eq hbal hG hN
  have hmemH : ∀ {L : Subgroup G}, L ∈ kStarComponents N → IsTwoComponentIn L H := by
    intro L hL
    have : L ∈ kStarComponents H := by rw [hHcomp]; exact hL
    exact this.1
  have hOb := h315c G hG N hN K hK b hbK hb2
  have hJCb : J ∈ kStarComponents Cb := ⟨hJ, hJs⟩
  have hJq : IsQuasisimple ↥J := isQuasisimple_of_mem_kStarComponents_of_le hOb hJCb
  have hJperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJ.1 hJ.2
  have hJinv : ∃ x ∈ J, orderOf x = 2 := exists_orderOf_eq_two_of_mem_solomonKStar hJs
  have hJmax : IsSolomonMaximal J := hJs.1
  have hJcomm : ∀ L ∈ kStarComponents N, L ≠ K → ⁅J, L⁆ = ⊥ := by
    intro L hL hLK
    have hLCb : L ∈ kStarComponents Cb :=
      ⟨isTwoComponentIn_centralizer_of_ne h32 h315a h315c hG hN hK hL (Ne.symm hLK) hbK hb2,
        hL.2⟩
    exact commutator_eq_bot_of_mem_kStarComponents_of_le hOb hJCb hLCb
      (fun h => hJN (h ▸ hL))
  have hCzb : centralizer ((zpowers b : Subgroup G) : Set G) = Cb := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  obtain ⟨M, hM, hJM⟩ := exists_not_le_coreActionKernel_of_le_twoLayerIn hJperf hJH hJinv
  have hKH : IsTwoComponentIn K H := hmemH hK
  have hcomm_le : ∀ {L : Subgroup G}, ⁅J, L⁆ = ⊥ → J ≤ coreActionKernel L := by
    intro L hL j hj
    exact Sol78.mem_coreActionKernel_of_commute fun l hl =>
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hL hj)) l hl
  by_cases hMs : M ∈ solomonKStar G
  ·
    have hMN : M ∈ kStarComponents N := by rw [← hHcomp]; exact ⟨hM, hMs⟩
    by_cases hMK : M = K
    · rw [hMK] at hJM
      obtain ⟨K', hK', hK'K⟩ := exists_mem_kStarComponents_ne hN K
      obtain ⟨v, hvK', hv2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK'.2
      set Cv := centralizer ({v} : Set G) with hCvdef
      have hJv : J ≤ Cv := by
        intro j hj
        have h1 := commutator_eq_bot_iff_le_centralizer.mp (hJcomm K' hK' hK'K) hj
        rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp h1) v hvK').symm
      have hbv : b ∈ Cv := by
        have h1 := commutator_eq_bot_iff_le_centralizer.mp
          (commutator_eq_bot_of_mem_kStarComponents h315a hG hN hK hK' (Ne.symm hK'K)) hbK
        rw [mem_centralizer_singleton_iff]
        exact ((mem_centralizer_iff.mp h1) v hvK').symm
      have hJLv : J ≤ twoLayerIn Cv := by
        have hJ2 : IsTwoComponentIn J (Cv ⊓ Cb) :=
          ⟨le_inf hJv hJ.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJv hJ.1)
            inf_le_right hJ.2⟩
        have h1 := GrSLit.pLayer_inf_centralizer_le (Y := Cv) (A := zpowers b)
          (zpowers_le.mpr hbv) hU2
        rw [hCzb] at h1
        exact (le_twoLayerIn_of_isTwoComponentIn hJ2).trans h1
      have hKv : IsTwoComponentIn K Cv :=
        isTwoComponentIn_centralizer_of_ne h32 h315a h315c hG hN hK' hK hK'K hvK' hv2
      have hequiv := solomonEquiv_of_not_le_coreActionKernel hv2 hJ hJmax hJv hJLv hKv hJM
      obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
      have hKq : IsQuasisimple ↥K := isQuasisimple_of_mem_kStarComponents h315a hG hN hK
      have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
      have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
      have hOK : oddCoreIn K ≤ centralizer (K : Set G) :=
        ((oddCoreIn_le_of_isTwoComponentIn
          (isTwoComponentIn_of_le hK.1 hKD (solomonKStarOf_le N))).trans
          (h315a G hG N hN)).trans (centralizer_le hKD)
      have hJKC : J ≤ K ⊔ centralizer (K : Set G) :=
        hJH.trans (twoLayerIn_le_sup_centralizer hKH hOK)
      have hJm : ¬ J ≤ centralizer (K : Set G) := fun h =>
        hJM (hcomm_le (commutator_eq_bot_iff_le_centralizer.mpr h))
      have hJq' : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
        isQuasisimple_quotient_of_isPComponent hJ.1 hJ.2
      have hJperf' : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
      have hZK : Open.fusionZStar ↥K = center ↥K := by
        refine fusionZStar_eq_center_of_le' (Subgroup.isPerfect_iff.mpr hKperf).commutator_eq_top
          fun x hx => ?_
        have hx' : (x : G) ∈ oddCoreIn K := ⟨x, hx, rfl⟩
        rw [mem_center_iff]
        intro y
        exact Subtype.ext ((mem_centralizer_iff.mp (hOK hx')) y y.2)
      have hcard : Nat.card (↥K ⧸ center ↥K) ≤ Nat.card (↥J ⧸ Open.fusionZStar ↥J) := by
        rw [← hZK, Nat.card_congr e.toEquiv]
      have hKb : K ≤ Cb :=
        le_centralizer_of_le_sup_centralizer hKperf hbK hJKC hJ.1 hJperf' hJq' hJm hcard
      have hKL : K ≤ twoLayerIn Cb := by
        have hbQ : zpowers b ≤ coreActionKernel K := by
          rw [zpowers_le]
          exact Sol78.mem_coreActionKernel_of_commute fun k hk =>
            mem_centralizer_singleton_iff.mp (hKb hk)
        have hbne : zpowers b ≠ ⊥ := by
          intro h
          rw [zpowers_eq_bot] at h
          rw [h, orderOf_one] at hb2
          norm_num at hb2
        have h1 := lemma212Input G K (zpowers b) hK.2 hbne hU2 hbQ
        rw [hCzb, inf_eq_left.mpr hKb, twoLayerIn_eq_self_of_isTwoComponentIn hK.1] at h1
        exact h1.trans (solomonKStarOf_le_twoLayerIn Cb)
      have hJNK : J ≤ normalizer (K : Set G) :=
        hJH.trans (FooteLit.twoLayerIn_le_normalizer hKH.1 hKH.2)
      have hKNJ : K ≤ normalizer (J : Set G) :=
        hKL.trans (FooteLit.twoLayerIn_le_normalizer hJ.1 hJ.2)
      have hne : ⁅J, K⁆ ≠ ⊥ := fun h => hJm (commutator_eq_bot_iff_le_centralizer.mp h)
      have hJK := eq_of_le_normalizer_of_commutator_ne_bot hJq hKq hJNK hKNJ hne
      exact hJN (hJK ▸ hK)
    · exact hJM (hcomm_le (hJcomm M hMN hMK))
  ·
    have hMK : M ≠ K := fun h => hMs (h ▸ hK.2)
    have hbN : b ∈ normalizer (M : Set G) :=
      ((le_twoLayerIn_of_isTwoComponentIn hKH).trans
        (FooteLit.twoLayerIn_le_normalizer hM.1 hM.2)) hbK
    have hbM : b ∈ coreActionKernel M := by
      rw [mem_coreActionKernel]
      refine ⟨hbN, fun m hm => ?_⟩
      have h1 : m⁻¹ * b⁻¹ * m * b ∈ oddCoreIn H := by
        have := FooteLit.commutator_le_oddCoreIn_of_ne hM hKH hMK
          (commutator_mem_commutator (inv_mem hm) (inv_mem hbK))
        rwa [commutatorElement_def, inv_inv, inv_inv] at this
      have h2 : m⁻¹ * b⁻¹ * m * b ∈ M := by
        have h3 : b⁻¹ * m * b⁻¹⁻¹ ∈ M := (mem_normalizer_iff.mp (inv_mem hbN) m).mp hm
        rw [inv_inv] at h3
        rw [mul_assoc, mul_assoc]
        refine mul_mem (inv_mem hm) ?_
        simpa [mul_assoc] using h3
      exact oddCoreIn_inf_le hM.1 (mem_inf.mpr ⟨h1, h2⟩)
    have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
      isQuasisimple_quotient_of_isPComponent hM.1 hM.2
    have hbQ : zpowers b ≤ coreActionKernel M := zpowers_le.mpr hbM
    have hcov := inf_centralizer_sup_oddCoreIn_eq hU2 hbQ
    rw [hCzb] at hcov
    obtain ⟨hMb2, hMbL, hMbsup, ⟨eMb⟩⟩ := cover_facts hMq inf_le_left hcov
    set Mb := oddResidualIn (M ⊓ Cb) with hMbdef
    set Y := H ⊓ Cb with hY
    have hYH : Y ≤ H := inf_le_left
    have hMCbY : M ⊓ Cb ≤ Y := inf_le_inf_right Cb hM.1
    have hMY : ((M ⊓ Cb).subgroupOf Y).IsSubnormal := by
      obtain ⟨-, -, hsub, -, -⟩ := hM.2
      have h1 := hsub.comap (Subgroup.inclusion hYH)
      have h2 : (M ⊓ Cb).subgroupOf Y = (M.subgroupOf H).comap (Subgroup.inclusion hYH) := by
        ext x
        simp only [mem_subgroupOf, mem_comap, coe_inclusion, mem_inf]
        exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).2⟩⟩
      rw [h2]
      exact h1
    have hMbY : IsTwoComponentIn Mb Y :=
      ⟨hMb2.1.trans hMCbY,
        GrSLit.isPComponent_subgroupOf_of_isSubnormal hMb2.1 hMCbY hMY hMb2.2⟩
    have hJHle : J ≤ H := hJH.trans (map_subtype_le _)
    have hJY : IsTwoComponentIn J Y :=
      ⟨le_inf hJHle hJ.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJHle hJ.1)
        inf_le_right hJ.2⟩
    have hMbM : Mb ≤ M := hMb2.1.trans inf_le_left
    have hOMb : oddCoreIn Mb ≤ oddCoreIn M := oddCoreIn_le_of_sup_eq hMbM hMbsup
    have hJMb : ¬ J ≤ coreActionKernel Mb := by
      intro hJMb'
      apply hJM
      intro j hj
      have hjN : j ∈ normalizer (M : Set G) :=
        (hJH.trans (FooteLit.twoLayerIn_le_normalizer hM.1 hM.2)) hj
      have hjO : j ∈ normalizer (oddCoreIn M : Set G) :=
        mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hjN)
      rw [mem_coreActionKernel]
      refine ⟨hjN, fun m hm => ?_⟩
      have hMbN : Mb ≤ normalizer (oddCoreIn M : Set G) :=
        hMbM.trans (le_normalizer_oddCoreIn M)
      have hm' : m ∈ oddCoreIn M ⊔ Mb := by rw [sup_comm, hMbsup]; exact hm
      obtain ⟨o, ho, m₁, hm₁, rfl⟩ := exists_mul_of_mem_sup_normalizer hMbN hm'
      have h1 : m₁⁻¹ * j⁻¹ * m₁ * j ∈ oddCoreIn M :=
        hOMb ((mem_coreActionKernel.mp (hJMb' hj)).2 m₁ hm₁)
      have h2 : j⁻¹ * o * j ∈ oddCoreIn M := by
        have := (mem_normalizer_iff.mp (inv_mem hjO) o).mp ho
        rwa [inv_inv] at this
      have h3 : o⁻¹ * (j⁻¹ * o * j) ∈ oddCoreIn M := mul_mem (inv_mem ho) h2
      have h4 : m₁⁻¹ * (o⁻¹ * (j⁻¹ * o * j)) * m₁ ∈ oddCoreIn M := by
        have := (mem_normalizer_iff.mp (hMbN (inv_mem hm₁)) _).mp h3
        rwa [inv_inv] at this
      have e : (o * m₁)⁻¹ * j⁻¹ * (o * m₁) * j =
          m₁⁻¹ * (o⁻¹ * (j⁻¹ * o * j)) * m₁ * (m₁⁻¹ * j⁻¹ * m₁ * j) := by group
      rw [e]
      exact mul_mem h4 h1
    have hJeq : J = Mb := by
      by_contra hne
      apply hJMb
      intro j hj
      have hjN : j ∈ normalizer (Mb : Set G) :=
        ((le_twoLayerIn_of_isTwoComponentIn hJY).trans
          (FooteLit.twoLayerIn_le_normalizer hMbY.1 hMbY.2)) hj
      rw [mem_coreActionKernel]
      refine ⟨hjN, fun m hm => ?_⟩
      have h1 : m⁻¹ * j⁻¹ * m * j ∈ oddCoreIn Y := by
        have := FooteLit.commutator_le_oddCoreIn_of_ne hMbY hJY (Ne.symm hne)
          (commutator_mem_commutator (inv_mem hm) (inv_mem hj))
        rwa [commutatorElement_def, inv_inv, inv_inv] at this
      have h2 : m⁻¹ * j⁻¹ * m * j ∈ Mb := by
        have h3 : j⁻¹ * m * j⁻¹⁻¹ ∈ Mb := (mem_normalizer_iff.mp (inv_mem hjN) m).mp hm
        rw [inv_inv] at h3
        rw [mul_assoc, mul_assoc]
        refine mul_mem (inv_mem hm) ?_
        simpa [mul_assoc] using h3
      exact oddCoreIn_inf_le hMbY.1 (mem_inf.mpr ⟨h1, h2⟩)
    have hMbCb : IsTwoComponentIn Mb Cb := hJeq ▸ hJ
    have hMbs : Mb ∈ solomonKStar G := hJeq ▸ hJs
    have hMperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hM.1 hM.2
    have hbne : zpowers b ≠ ⊥ := by
      intro h
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hb2
      norm_num at hb2
    have hMbT : IsTwoComponentIn (twoLayerIn (M ⊓ centralizer ((zpowers b : Subgroup G) : Set G)))
        (centralizer ((zpowers b : Subgroup G) : Set G)) := by
      rw [hCzb, hMbL]
      exact hMbCb
    have hMmem : IsSolomonMember M := isSolomonMember_of_twoLayerIn hMperf hMq hbne hU2 hbQ hMbT
    have hMbmem : IsSolomonMember Mb := hMbs.1.1
    have hlt : SolomonLt M Mb := by
      refine ⟨hMmem, hMbmem, zpowers b, hU2, hbQ, ?_⟩
      rw [hCzb, hMbL]
      have hMbperf : ⁅Mb, Mb⁆ = Mb := UnbalancedCorr.commutator_eq_of_isPComponent hMbCb.1 hMbCb.2
      exact isTwoComponentIn_conjClosure_of_not_le hMbCb (le_twoLayerIn_of_isTwoComponentIn hMbCb)
        (not_le_coreActionKernel_of_le le_rfl hMbperf
          (exists_orderOf_eq_two_of_mem_solomonKStar hMbs))
    have hlink : SolomonLink M Mb := ⟨⟨Sol78.fusionZStarQuotOfCore eMb.symm⟩, Or.inl hlt⟩
    have hMeq : SolomonEquiv Mb M := ⟨hMbmem, Relation.ReflTransGen.single (solomonLink_symm hlink)⟩
    exact hMs (mem_solomonKStar_of_solomonEquiv hMbs hMeq)

theorem lemma316ProductInputFor_of_steps (h32 : Lemma32InputFor 𝒜)
    (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hbal : Lemma316BalancedInputFor 𝒜) : Lemma316ProductInputFor 𝒜 :=
  fun _ _ _ hG _ hN _ hK _ hbK hb2 _ hJ hJs hJH =>
    mem_kStarComponents_of_steps h32 h315a h315c hbal hG hN hK hbK hb2 hJ hJs hJH

theorem lemma316InputFor_of_steps (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜) : Lemma316InputFor 𝒜 :=
  lemma316InputFor_of_inputs h32 h315a h315c hbal
    (lemma316ProductInputFor_of_steps h32 h315a h315c hbal)

end CFSG.ComponentClassification.Sol76T13
