module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316L33

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_oddResidualIn_of_not_le_coreActionKernel {H P J : Subgroup G} {b : G}
    (hP : IsTwoComponentIn P H) (hbP : b ∈ coreActionKernel P) (hb2 : orderOf b = 2)
    (hJ : IsTwoComponentIn J (centralizer ({b} : Set G))) (hJH : J ≤ twoLayerIn H)
    (hJP : ¬ J ≤ coreActionKernel P) :
    J = oddResidualIn (P ⊓ centralizer ({b} : Set G)) ∧
      twoLayerIn (P ⊓ centralizer ({b} : Set G)) = oddResidualIn (P ⊓ centralizer ({b} : Set G)) ∧
      Nonempty (↥(oddResidualIn (P ⊓ centralizer ({b} : Set G))) ⧸
          pPrimeCore 2 ↥(oddResidualIn (P ⊓ centralizer ({b} : Set G))) ≃*
        ↥P ⧸ pPrimeCore 2 ↥P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cb := centralizer ({b} : Set G) with hCb
  have hCzb : centralizer ((zpowers b : Subgroup G) : Set G) = Cb := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hPq : IsQuasisimple (↥P ⧸ pPrimeCore 2 ↥P) :=
    isQuasisimple_quotient_of_isPComponent hP.1 hP.2
  have hbQ : zpowers b ≤ coreActionKernel P := zpowers_le.mpr hbP
  have hcov := inf_centralizer_sup_oddCoreIn_eq hU2 hbQ
  rw [hCzb] at hcov
  obtain ⟨hPb2, hPbL, hPbsup, ePb⟩ := cover_facts hPq inf_le_left hcov
  set Pb := oddResidualIn (P ⊓ Cb) with hPbdef
  set Y := H ⊓ Cb with hY
  have hYH : Y ≤ H := inf_le_left
  have hPCbY : P ⊓ Cb ≤ Y := inf_le_inf_right Cb hP.1
  have hPY : ((P ⊓ Cb).subgroupOf Y).IsSubnormal := by
    obtain ⟨-, -, hsub, -, -⟩ := hP.2
    have h1 := hsub.comap (Subgroup.inclusion hYH)
    have h2 : (P ⊓ Cb).subgroupOf Y = (P.subgroupOf H).comap (Subgroup.inclusion hYH) := by
      ext x
      simp only [mem_subgroupOf, mem_comap, coe_inclusion, mem_inf]
      exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp x.2).2⟩⟩
    rw [h2]
    exact h1
  have hPbY : IsTwoComponentIn Pb Y :=
    ⟨hPb2.1.trans hPCbY, GrSLit.isPComponent_subgroupOf_of_isSubnormal hPb2.1 hPCbY hPY hPb2.2⟩
  have hJHle : J ≤ H := hJH.trans (map_subtype_le _)
  have hJY : IsTwoComponentIn J Y :=
    ⟨le_inf hJHle hJ.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJHle hJ.1)
      inf_le_right hJ.2⟩
  have hPbP : Pb ≤ P := hPb2.1.trans inf_le_left
  have hOPb : oddCoreIn Pb ≤ oddCoreIn P := oddCoreIn_le_of_sup_eq hPbP hPbsup
  have hJPb : ¬ J ≤ coreActionKernel Pb := by
    intro hJPb'
    apply hJP
    intro j hj
    have hjN : j ∈ normalizer (P : Set G) :=
      (hJH.trans (FooteLit.twoLayerIn_le_normalizer hP.1 hP.2)) hj
    have hjO : j ∈ normalizer (oddCoreIn P : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hjN)
    rw [mem_coreActionKernel]
    refine ⟨hjN, fun m hm => ?_⟩
    have hPbN : Pb ≤ normalizer (oddCoreIn P : Set G) :=
      hPbP.trans (le_normalizer_oddCoreIn P)
    have hm' : m ∈ oddCoreIn P ⊔ Pb := by rw [sup_comm, hPbsup]; exact hm
    obtain ⟨o, ho, m₁, hm₁, rfl⟩ := exists_mul_of_mem_sup_normalizer hPbN hm'
    have h1 : m₁⁻¹ * j⁻¹ * m₁ * j ∈ oddCoreIn P :=
      hOPb ((mem_coreActionKernel.mp (hJPb' hj)).2 m₁ hm₁)
    have h2 : j⁻¹ * o * j ∈ oddCoreIn P := by
      have := (mem_normalizer_iff.mp (inv_mem hjO) o).mp ho
      rwa [inv_inv] at this
    have h3 : o⁻¹ * (j⁻¹ * o * j) ∈ oddCoreIn P := mul_mem (inv_mem ho) h2
    have h4 : m₁⁻¹ * (o⁻¹ * (j⁻¹ * o * j)) * m₁ ∈ oddCoreIn P := by
      have := (mem_normalizer_iff.mp (hPbN (inv_mem hm₁)) _).mp h3
      rwa [inv_inv] at this
    have e : (o * m₁)⁻¹ * j⁻¹ * (o * m₁) * j =
        m₁⁻¹ * (o⁻¹ * (j⁻¹ * o * j)) * m₁ * (m₁⁻¹ * j⁻¹ * m₁ * j) := by group
    rw [e]
    exact mul_mem h4 h1
  refine ⟨?_, hPbL, ePb⟩
  by_contra hne
  apply hJPb
  intro j hj
  have hjN : j ∈ normalizer (Pb : Set G) :=
    ((le_twoLayerIn_of_isTwoComponentIn hJY).trans
      (FooteLit.twoLayerIn_le_normalizer hPbY.1 hPbY.2)) hj
  rw [mem_coreActionKernel]
  refine ⟨hjN, fun m hm => ?_⟩
  have h1 : m⁻¹ * j⁻¹ * m * j ∈ oddCoreIn Y := by
    have := FooteLit.commutator_le_oddCoreIn_of_ne hPbY hJY (Ne.symm hne)
      (commutator_mem_commutator (inv_mem hm) (inv_mem hj))
    rwa [commutatorElement_def, inv_inv, inv_inv] at this
  have h2 : m⁻¹ * j⁻¹ * m * j ∈ Pb := by
    have h3 : j⁻¹ * m * j⁻¹⁻¹ ∈ Pb := (mem_normalizer_iff.mp (inv_mem hjN) m).mp hm
    rw [inv_inv] at h3
    rw [mul_assoc, mul_assoc]
    refine mul_mem (inv_mem hm) ?_
    simpa [mul_assoc] using h3
  exact oddCoreIn_inf_le hPbY.1 (mem_inf.mpr ⟨h1, h2⟩)

omit [Finite G] in
theorem mem_coreActionKernel_of_le_sup {K J : Subgroup G} {s : G} (hsK : s ∈ K)
    (hJN : J ≤ normalizer (K : Set G)) (hKJ : K ≤ coreActionKernel K ⊔ J)
    (hJs : J ≤ centralizer ({s} : Set G)) : s ∈ coreActionKernel K := by
  refine ⟨le_normalizer hsK, fun x hx => ?_⟩
  have hJQ : J ≤ normalizer (coreActionKernel K : Set G) := fun j hj =>
    FooteLit.mem_normalizer_coreActionKernel (hJN hj)
  obtain ⟨q, hq, j, hj, rfl⟩ := exists_mul_of_mem_sup_normalizer hJQ (hKJ hx)
  have hjs : j * s = s * j := mem_centralizer_singleton_iff.mp (hJs hj)
  have h1 : s⁻¹ * q⁻¹ * s * q ∈ oddCoreIn K := hq.2 s hsK
  have hjO : j⁻¹ ∈ normalizer (oddCoreIn K : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (inv_mem (hJN hj)))
  have h2 : j⁻¹ * (s⁻¹ * q⁻¹ * s * q)⁻¹ * j⁻¹⁻¹ ∈ oddCoreIn K :=
    (mem_normalizer_iff.mp hjO _).mp (inv_mem h1)
  have e : (q * j)⁻¹ * s⁻¹ * (q * j) * s = j⁻¹ * (s⁻¹ * q⁻¹ * s * q)⁻¹ * j⁻¹⁻¹ := by
    have hjs' : s⁻¹ * j = j * s⁻¹ := by
      calc s⁻¹ * j = s⁻¹ * (j * s) * s⁻¹ := by group
        _ = s⁻¹ * (s * j) * s⁻¹ := by rw [hjs]
        _ = j * s⁻¹ := by group
    calc (q * j)⁻¹ * s⁻¹ * (q * j) * s = j⁻¹ * q⁻¹ * (s⁻¹ * q) * (j * s) := by group
      _ = j⁻¹ * q⁻¹ * (s⁻¹ * q) * (s * j) := by rw [hjs]
      _ = j⁻¹ * (q⁻¹ * s⁻¹ * q * s) * j := by group
      _ = j⁻¹ * (s⁻¹ * q⁻¹ * s * q)⁻¹ * j⁻¹⁻¹ := by group
  rw [e]
  exact h2

theorem exists_eq_twoLayerIn_inf_of_mem_kStarComponents (hq : QuasisimpleTwoPartInput)
    (hG : KStarKProper G) {N : Subgroup G}
    (hr : ∃ K₁ ∈ kStarComponents N, ∃ K₂ ∈ kStarComponents N, K₁ ≠ K₂)
    (hKH : solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N)
    (hCb : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G))
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2)
    {J : Subgroup G} (hJ : J ∈ kStarComponents (centralizer ({b} : Set G))) :
    ∃ L ∈ kStarComponents N, b ∈ coreActionKernel L ∧
      J = twoLayerIn (L ⊓ centralizer ({b} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := solomonKStarOf N with hD
  set H := normalizer (D : Set G) with hH
  set Cb := centralizer ({b} : Set G) with hCbdef
  have hHcomp : kStarComponents H = kStarComponents N :=
    kStarComponents_normalizer_eq_of_solomonKStarOf_eq hKH
  have hKHc : IsTwoComponentIn K H := (mem_kStarComponents_normalizer hK).1
  have hCbH : Cb ≤ H := hCb K hK b hbK hb2
  have hJC : IsTwoComponentIn J Cb := hJ.1
  have hJs : J ∈ solomonKStar G := hJ.2
  have hJperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJC.1 hJC.2
  have hJinv : ∃ x ∈ J, orderOf x = 2 := exists_orderOf_eq_two_of_mem_solomonKStar hJs
  have hCzb : centralizer ((zpowers b : Subgroup G) : Set G) = Cb := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hU2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hbH : b ∈ H := le_normalizer (hKD hbK)
  have hJH : J ≤ twoLayerIn H := by
    have h1 := GrSLit.pLayer_inf_centralizer_le (Y := H) (A := zpowers b) (zpowers_le.mpr hbH) hU2
    rw [hCzb, inf_eq_right.mpr hCbH] at h1
    exact (le_twoLayerIn_of_isTwoComponentIn hJC).trans h1
  obtain ⟨P, hP, hJP⟩ := exists_not_le_coreActionKernel_of_le_twoLayerIn hJperf hJH hJinv
  by_cases hPs : P ∈ solomonKStar G
  · have hPN : P ∈ kStarComponents N := by rw [← hHcomp]; exact ⟨hP, hPs⟩
    by_cases hPK : P = K
    · rw [hPK] at hJP
      set Q := coreActionKernel K with hQ
      have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
        isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
      have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
        isQuasisimple_quotient_of_isPComponent hJC.1 hJC.2
      have hJres : oddResidualIn J = J := oddResidualIn_eq_self_of_isPComponent hJC.1 hJC.2
      have hJNK : J ≤ normalizer (K : Set G) :=
        hJH.trans (FooteLit.twoLayerIn_le_normalizer hKHc.1 hKHc.2)
      have hJNQ : J ≤ normalizer (Q : Set G) := fun j hj =>
        FooteLit.mem_normalizer_coreActionKernel (hJNK hj)
      have hKNQ : K ≤ normalizer (Q : Set G) := fun k hk =>
        FooteLit.mem_normalizer_coreActionKernel (le_normalizer hk)
      have hLHKQ : twoLayerIn H ≤ K ⊔ Q := twoLayerIn_le_of_forall fun P' hP' => by
        by_cases h : P' = K
        · rw [h]
          exact le_sup_left
        · exact (GSThmB.B5a.le_coreActionKernel_of_ne hKHc.1 hP'.1 hKHc.2 hP'.2
            (Ne.symm h)).trans le_sup_right
      have hJKQ : J ≤ K ⊔ Q := hJH.trans hLHKQ
      obtain ⟨K', hK', hK'K⟩ := exists_mem_ne_of_two hr K
      have hbK' : b ∈ coreActionKernel K' := mem_coreActionKernel_of_ne hK hK' (Ne.symm hK'K) hbK
      have hK'b := isTwoComponentIn_twoLayerIn_inf_centralizer hq hG hCb hK' hb2 hbK'
      obtain ⟨hK'b2, -, -, -, hK'br⟩ := pump_facts hK' hbK' hb2
      obtain ⟨v, hvK'b, hv2⟩ :=
        exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hK'br)
      have hvK' : v ∈ K' := (hK'b2.1.trans inf_le_left) hvK'b
      have hK'Q : K' ≤ Q := GSThmB.B5a.le_coreActionKernel_of_ne hKHc.1
        (mem_kStarComponents_normalizer hK').1.1 hKHc.2 (mem_kStarComponents_normalizer hK').1.2
        (Ne.symm hK'K)
      have hJne : twoLayerIn (K' ⊓ Cb) ≠ J := fun h => hJP (by
        rw [← h]
        exact (hK'b2.1.trans inf_le_left).trans hK'Q)
      have hvJ : v ∈ coreActionKernel J :=
        GSThmB.B5a.le_coreActionKernel_of_ne hJC.1 hK'b.1.1 hJC.2 hK'b.1.2 (Ne.symm hJne) hvK'b
      obtain ⟨hJv2, hJvsup, -, hJv212, -⟩ := pump_facts hJ hvJ hv2
      set Cv := centralizer ({v} : Set G) with hCv
      set Jv := twoLayerIn (J ⊓ Cv) with hJv
      have hJvL : Jv ≤ twoLayerIn Cv := hJv212.trans (solomonKStarOf_le_twoLayerIn Cv)
      have hvK : v ∈ coreActionKernel K := hK'Q hvK'
      have hKv := isTwoComponentIn_twoLayerIn_inf_centralizer hq hG hCb hK hv2 hvK
      obtain ⟨hKv2, hKvsup, ⟨eKv⟩, -, -⟩ := pump_facts hK hvK hv2
      set Kv := twoLayerIn (K ⊓ Cv) with hKvdef
      have hJvKv : ¬ Jv ≤ coreActionKernel Kv := by
        intro h
        apply hJP
        have h1 : Jv ≤ Q := fun x hx =>
          FooteLit.mem_coreActionKernel_of_sup (hKv2.1.trans inf_le_left) hKvsup
            (hJNK ((hJv2.1.trans inf_le_left) hx)) (h hx)
        have hOJQ : oddCoreIn J ≤ normalizer (Q : Set G) := fun x hx => hJNQ ((map_subtype_le _) hx)
        exact le_of_le_sup_of_coprime hJres hOJQ (coprime_card_oddCoreIn J)
          (hJvsup.symm.le.trans (sup_le_sup_right h1 _))
      have hKvP : IsTwoComponentIn Kv (conjClosure Jv (twoLayerIn Cv)) :=
        isTwoComponentIn_conjClosure_of_not_le hKv.1 hJvL hJvKv
      have hCzv : centralizer ((zpowers v : Subgroup G) : Set G) = Cv := by
        rw [zpowers_eq_closure, centralizer_closure]
      have hV2 : IsPGroup 2 (zpowers v) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
      have hlt : SolomonLt J Kv := by
        refine ⟨hJs.1.1, hKv.2.1.1, zpowers v, hV2, zpowers_le.mpr hvJ, ?_⟩
        rw [hCzv]
        exact hKvP
      have heq : SolomonEquiv J Kv := hJs.1.2 J Kv ⟨hJs.1.1, Relation.ReflTransGen.refl⟩ hlt
      obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen heq.2
      have hcard : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) := by
        rw [Nat.card_congr e.toEquiv, Nat.card_congr eKv.toEquiv]
      have hKJQ : K ≤ J ⊔ Q :=
        le_sup_coreActionKernel_of_card_fusionZStar hJq hJres hKNQ hJNQ hJKQ hJP hcard
      have hbQ : b ∈ Q := by
        refine mem_coreActionKernel_of_le_sup hbK hJNK ?_ hJC.1
        rw [sup_comm]
        exact hKJQ
      have hKb := isTwoComponentIn_twoLayerIn_inf_centralizer hq hG hCb hK hb2 hbQ
      obtain ⟨hKb2, hKbsup, -, -, -⟩ := pump_facts hK hbQ hb2
      refine ⟨K, hK, hbQ, ?_⟩
      by_contra hne
      apply hJP
      have h1 : J ≤ coreActionKernel (twoLayerIn (K ⊓ Cb)) :=
        GSThmB.B5a.le_coreActionKernel_of_ne hKb.1.1 hJC.1 hKb.1.2 hJC.2 (Ne.symm hne)
      exact fun x hx => FooteLit.mem_coreActionKernel_of_sup (hKb2.1.trans inf_le_left) hKbsup
        (hJNK hx) (h1 hx)
    ·
      have hbP : b ∈ coreActionKernel P :=
        GSThmB.B5a.le_coreActionKernel_of_ne hP.1 hKHc.1 hP.2 hKHc.2 hPK hbK
      obtain ⟨hJeq, hPbL, -⟩ := eq_oddResidualIn_of_not_le_coreActionKernel hP hbP hb2 hJC hJH hJP
      exact ⟨P, hPN, hbP, hJeq.trans hPbL.symm⟩
  ·
    exfalso
    have hPK : P ≠ K := fun h => hPs (h ▸ hK.2)
    have hbP : b ∈ coreActionKernel P :=
      GSThmB.B5a.le_coreActionKernel_of_ne hP.1 hKHc.1 hP.2 hKHc.2 hPK hbK
    obtain ⟨hJeq, hPbL, ⟨ePb⟩⟩ :=
      eq_oddResidualIn_of_not_le_coreActionKernel hP hbP hb2 hJC hJH hJP
    set Pb := oddResidualIn (P ⊓ Cb) with hPbdef
    have hPbCb : IsTwoComponentIn Pb Cb := hJeq ▸ hJC
    have hPbs : Pb ∈ solomonKStar G := hJeq ▸ hJs
    have hPq : IsQuasisimple (↥P ⧸ pPrimeCore 2 ↥P) :=
      isQuasisimple_quotient_of_isPComponent hP.1 hP.2
    have hPperf : ⁅P, P⁆ = P := UnbalancedCorr.commutator_eq_of_isPComponent hP.1 hP.2
    have hbne : zpowers b ≠ ⊥ := by
      intro h
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at hb2
      norm_num at hb2
    have hbQ : zpowers b ≤ coreActionKernel P := zpowers_le.mpr hbP
    have hPbT : IsTwoComponentIn (twoLayerIn (P ⊓ centralizer ((zpowers b : Subgroup G) : Set G)))
        (centralizer ((zpowers b : Subgroup G) : Set G)) := by
      rw [hCzb, hPbL]
      exact hPbCb
    have hPmem : IsSolomonMember P := isSolomonMember_of_twoLayerIn hPperf hPq hbne hU2 hbQ hPbT
    have hPbmem : IsSolomonMember Pb := hPbs.1.1
    have hlt : SolomonLt P Pb := by
      refine ⟨hPmem, hPbmem, zpowers b, hU2, hbQ, ?_⟩
      rw [hCzb, hPbL]
      have hPbperf : ⁅Pb, Pb⁆ = Pb :=
        UnbalancedCorr.commutator_eq_of_isPComponent hPbCb.1 hPbCb.2
      exact isTwoComponentIn_conjClosure_of_not_le hPbCb (le_twoLayerIn_of_isTwoComponentIn hPbCb)
        (not_le_coreActionKernel_of_le le_rfl hPbperf
          (exists_orderOf_eq_two_of_mem_solomonKStar hPbs))
    have hlink : SolomonLink P Pb := ⟨⟨Sol78.fusionZStarQuotOfCore ePb.symm⟩, Or.inl hlt⟩
    have hPeq : SolomonEquiv Pb P :=
      ⟨hPbmem, Relation.ReflTransGen.single (solomonLink_symm hlink)⟩
    exact hPs (mem_solomonKStar_of_solomonEquiv hPbs hPeq)

end CFSG.ComponentClassification.Sol76T13
