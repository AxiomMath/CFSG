module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSkeleton

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def FooteOddCoreReduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → pPrimeCore 2 G = ⊥

@[expose] def FooteComponentReduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → pPrimeCore 2 G = ⊥ →
    conjClosure L (pLayer G 2) ⊔ zpowers t = ⊤

@[expose] def FooteRankOneBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → pPrimeCore 2 G = ⊥ →
    conjClosure L (pLayer G 2) ⊔ zpowers t = ⊤ →
    IsSimpleGroup ↥(conjClosure L (pLayer G 2)) →
    ∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2

@[expose] def FooteOuterReduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), FooteMinimal G →
    FooteCounterexample G t L → pPrimeCore 2 G = ⊥ →
    conjClosure L (pLayer G 2) ⊔ zpowers t = ⊤ →
    IsSimpleGroup ↥(conjClosure L (pLayer G 2)) →
    (∀ A ∈ footeFamilyOf L, CFSG.pRank 2 ↥A = 2) →
    conjClosure L (pLayer G 2) = ⊤

variable {G : Type} [Group G] [Finite G]

theorem isPComponent_subgroupOf_top_iff' {K : Subgroup G} :
    IsPComponent 2 (K.subgroupOf ⊤) ↔ IsPComponent 2 K := by
  rw [(LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    (Subgroup.topEquiv (G := G))).1]
  congr! 1
  ext x
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hx
    exact ⟨⟨x, mem_top x⟩, hx, rfl⟩

theorem sup_oddCoreIn_eq_of_card_le {K M : Subgroup G} (hKM : K ≤ M)
    (hcard : Nat.card (M ⧸ pPrimeCore 2 M) ≤ Nat.card (K ⧸ pPrimeCore 2 K)) :
    K ⊔ oddCoreIn M = M := by
  classical
  set ι : K →* M := Subgroup.inclusion hKM with hι
  set ψ : K →* M ⧸ pPrimeCore 2 M := (QuotientGroup.mk' _).comp ι with hψ
  have hKO : K ⊓ oddCoreIn M ≤ oddCoreIn K :=
    le_oddCoreIn inf_le_left (fun k hk => mem_normalizer_inf' (le_normalizer hk)
      (mem_normalizer_oddCoreIn (le_normalizer (hKM hk))))
      (Odd.of_dvd_nat (odd_card_oddCoreIn M) (card_dvd_of_le inf_le_right))
  have hker : ψ.ker ≤ pPrimeCore 2 K := by
    intro k hk
    have hkO : ι k ∈ pPrimeCore 2 M := (QuotientGroup.eq_one_iff _).mp hk
    rw [mem_pPrimeCore_iff_mem_oddCoreIn] at hkO ⊢
    exact hKO (mem_inf.mpr ⟨k.2, hkO⟩)
  have hrange : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [← Subgroup.index_ker]
    exact hcard.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker))
  refine le_antisymm (sup_le hKM (map_subtype_le _)) fun m hm => ?_
  obtain ⟨k, hk⟩ := (MonoidHom.mem_range).mp (hrange ▸ mem_top (QuotientGroup.mk ⟨m, hm⟩ :
    M ⧸ pPrimeCore 2 M))
  have hko : (ι k)⁻¹ * ⟨m, hm⟩ ∈ pPrimeCore 2 M := QuotientGroup.eq.mp hk
  rw [mem_pPrimeCore_iff_mem_oddCoreIn] at hko
  rw [show m = (k : G) * ((k : G)⁻¹ * m) by group]
  exact mul_mem (mem_sup_left k.2) (mem_sup_right (by simpa [hι] using hko))

theorem exists_component_of_counterexample {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) :
    IsPComponent 2 (conjClosure L (pLayer G 2)) ∧
      conjugate (conjClosure L (pLayer G 2)) t = conjClosure L (pLayer G 2) ∧
      L ≤ conjClosure L (pLayer G 2) ∧
      L ⊔ oddCoreIn (conjClosure L (pLayer G 2)) < conjClosure L (pLayer G 2) ∧
      IsEmpty (L ⧸ Open.fusionZStar L ≃*
        conjClosure L (pLayer G 2) ⧸ Open.fusionZStar (conjClosure L (pLayer G 2))) := by
  obtain ⟨⟨-, -, ⟨ht, hLt, hLpc⟩, -, -, -⟩, hcon⟩ := hce
  obtain ⟨G₀, hG₀, hLG₀, hA, hcase⟩ := foote_lemma_2_1_iv ht hLt hLpc
  rcases hcase with ⟨hG₀t, -, ⟨e⟩⟩ | ⟨hG₀t, hlt, hiso⟩ | ⟨hne, -, -⟩
  · exfalso
    apply hcon
    have hA' : conjClosure L (pLayer G 2) = G₀ := by rw [hA, hG₀t, sup_idem]
    rw [hA']
    exact Or.inl ⟨e.symm⟩
  · have hA' : conjClosure L (pLayer G 2) = G₀ := by rw [hA, hG₀t, sup_idem]
    rw [hA']
    refine ⟨hG₀, hG₀t, ?_, hlt, hiso⟩
    rwa [hG₀t, sup_idem] at hLG₀
  · exfalso
    apply hcon
    rw [hA]
    exact Or.inr (Or.inl ⟨G₀, hG₀, hne, rfl⟩)

theorem oddCoreOfCentralizer_eq_bot_of_eq_top (hO : pPrimeCore 2 G = ⊥) {z : G}
    (hz : centralizer ({z} : Set G) = ⊤) : oddCoreOfCentralizer z = ⊥ := by
  have hsub : (centralizer ({z} : Set G)).IsSubnormal := by
    rw [hz]; exact Subgroup.IsSubnormal.top
  have h := Walter.map_pPrimeCore_le_of_isSubnormal hsub
  rw [hO] at h
  exact le_bot_iff.mp h

theorem twoLayerOf_eq_of_eq_top {z : G} (hz : centralizer ({z} : Set G) = ⊤) :
    twoLayerOf z = pLayer G 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold twoLayerOf
  rw [hz]
  have h := UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  rw [← h]
  rfl

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {Q : Type*} [Group Q]
    (hQ : IsQuasisimple Q) (hZ : center Q = ⊥) : IsSimpleGroup Q := by
  obtain ⟨-, hs, -⟩ := hQ
  have e : Q ⧸ center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem isSimpleGroup_conjClosure_of_counterexample {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) (hO : pPrimeCore 2 G = ⊥)
    (hgen : conjClosure L (pLayer G 2) ⊔ zpowers t = ⊤) :
    IsSimpleGroup ↥(conjClosure L (pLayer G 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hA2c, hAt, hLA, hlt, hiso⟩ := exists_component_of_counterexample hce
  obtain ⟨⟨-, -, ⟨ht, hLt, hLpc⟩, hmax, -, -⟩, -⟩ := hce
  generalize hAdef : conjClosure L (pLayer G 2) = A at *
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨-, -, hAsub, -, -⟩ := id hA2c
  have hOA : pPrimeCore 2 A = ⊥ := by
    have h := Walter.map_pPrimeCore_le_of_isSubnormal hAsub
    rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ (subtype_injective _)] at h
    exact h
  have hAq : IsQuasisimple A := by
    have hq := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 A hA2c
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hOA).trans QuotientGroup.quotientBot) hq
  refine isSimpleGroup_of_isQuasisimple_of_center_eq_bot hAq ?_
  by_contra hZ
  obtain ⟨v, hv⟩ : ∃ v : center A, orderOf v = 2 := by
    have hp : IsPGroup 2 (center A) := fun x => by
      obtain ⟨k, hk⟩ :=
        UnbalancedGS.SwappedCentralProduct.pow_two_pow_eq_one_of_mem_center hOA x.2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hnt : Nontrivial (center A) := (nontrivial_iff_ne_bot _).mpr hZ
    rcases hp.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne'
    · exact exists_prime_orderOf_dvd_card' 2 h
  set v₀ : G := ((v : A) : G) with hv₀
  have hv₀A : v₀ ∈ A := (v : A).2
  have hv₀c : ∀ y ∈ A, y * v₀ = v₀ * y := fun y hy =>
    congrArg Subtype.val (mem_center_iff.mp v.2 ⟨y, hy⟩)
  have hv₀2 : orderOf v₀ = 2 := by rw [hv₀, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hv]
  have hv₀v₀ : v₀ * v₀ = 1 := by rw [← sq, ← hv₀2, pow_orderOf_eq_one]
  have htA : t ∈ normalizer (A : Set G) := mem_normalizer_of_conjugate_eq hAt
  obtain ⟨w₀, hw₀⟩ : ∃ w : G, w = t * v₀ * t⁻¹ := ⟨_, rfl⟩
  have hw₀A : w₀ ∈ A := hw₀ ▸ (mem_normalizer_iff.mp htA v₀).mp hv₀A
  have hw₀c : ∀ y ∈ A, y * w₀ = w₀ * y := by
    intro y hy
    have hy' : t⁻¹ * y * t ∈ A := by
      have := (mem_normalizer_iff.mp (inv_mem htA) y).mp hy
      rwa [inv_inv] at this
    have h1 := hv₀c _ hy'
    calc y * w₀ = t * ((t⁻¹ * y * t) * v₀) * t⁻¹ := by rw [hw₀]; group
      _ = t * (v₀ * (t⁻¹ * y * t)) * t⁻¹ := by rw [h1]
      _ = w₀ * y := by rw [hw₀]; group
  have hw₀w₀ : w₀ * w₀ = 1 := by
    calc w₀ * w₀ = t * (v₀ * v₀) * t⁻¹ := by rw [hw₀]; group
      _ = 1 := by rw [hv₀v₀]; group
  have htw₀ : t * w₀ * t⁻¹ = v₀ := by
    calc t * w₀ * t⁻¹ = (t * t) * v₀ * (t * t)⁻¹ := by rw [hw₀]; group
      _ = v₀ := by rw [htt]; group
  obtain ⟨z, hzA, hzc, hz2, hzt⟩ : ∃ z : G, z ∈ A ∧ (∀ y ∈ A, y * z = z * y) ∧
      orderOf z = 2 ∧ t * z = z * t := by
    by_cases hvw : w₀ = v₀
    · refine ⟨v₀, hv₀A, hv₀c, hv₀2, ?_⟩
      calc t * v₀ = t * v₀ * t⁻¹ * t := by group
        _ = v₀ * t := by rw [← hw₀, hvw]
    · have hcomm : w₀ * v₀ = v₀ * w₀ := hv₀c w₀ hw₀A
      refine ⟨v₀ * w₀, mul_mem hv₀A hw₀A, fun y hy => ?_, ?_, ?_⟩
      · calc y * (v₀ * w₀) = (y * v₀) * w₀ := (mul_assoc _ _ _).symm
          _ = (v₀ * y) * w₀ := by rw [hv₀c y hy]
          _ = v₀ * (y * w₀) := mul_assoc _ _ _
          _ = v₀ * (w₀ * y) := by rw [hw₀c y hy]
          _ = v₀ * w₀ * y := (mul_assoc _ _ _).symm
      · refine orderOf_eq_prime ?_ ?_
        · rw [sq]
          calc v₀ * w₀ * (v₀ * w₀) = v₀ * (w₀ * v₀) * w₀ := by group
            _ = v₀ * (v₀ * w₀) * w₀ := by rw [hcomm]
            _ = 1 := by rw [← mul_assoc, hv₀v₀, one_mul, hw₀w₀]
        · intro h
          apply hvw
          have h1 : w₀ = v₀⁻¹ := eq_inv_of_mul_eq_one_right h
          rwa [inv_eq_of_mul_eq_one_right hv₀v₀] at h1
      · have h1 : t * (v₀ * w₀) * t⁻¹ = v₀ * w₀ := by
          calc t * (v₀ * w₀) * t⁻¹ = (t * v₀ * t⁻¹) * (t * w₀ * t⁻¹) := by group
            _ = w₀ * v₀ := by rw [← hw₀, htw₀]
            _ = v₀ * w₀ := hcomm
        calc t * (v₀ * w₀) = t * (v₀ * w₀) * t⁻¹ * t := by group
          _ = v₀ * w₀ * t := by rw [h1]
  have hCz : centralizer ({z} : Set G) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (hzc y hy)) ?_
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.mpr hzt
  have hLz : L ≤ centralizer ({z} : Set G) := by rw [hCz]; exact le_top
  have htz : t ≠ z := by
    intro h
    have hLG : IsPComponent 2 L := by
      rw [← isPComponent_subgroupOf_top_iff']
      have h1 := hLpc
      rw [show centralizer ({t} : Set G) = ⊤ by rw [h]; exact hCz] at h1
      exact h1
    have heq := (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two L A
      hLG hA2c).1 hLA
    rw [← heq] at hlt
    exact (lt_irrefl L) (lt_of_le_of_lt le_sup_left hlt)
  have hfix : footeFixed L z = L := by
    rw [footeFixed_eq_oddResidualIn, inf_eq_left.mpr hLz,
      oddCoreOfCentralizer_eq_bot_of_eq_top hO hCz, sup_bot_eq]
    exact oddResidualIn_eq_self_of_isPComponent hLt hLpc
  have hstep : FootePointedStep t L z A := by
    refine ⟨⟨ht, hLt, hLpc⟩, ⟨hz2, by rw [hCz]; exact le_top, ?_⟩, hzt, htz,
      GSLit.mem_coreActionKernel_of_le_centralizer hLz, ?_⟩
    · rw [hCz, isPComponent_subgroupOf_top_iff']
      exact hA2c
    · rw [hfix, twoLayerOf_eq_of_eq_top hCz, hAdef, hAt, sup_idem]
  obtain ⟨e⟩ := hmax.equiv_of_step hstep
  exact hiso.false e

theorem two_le_pRank_coreActionKernel_of_counterexample {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L) [IsSimpleGroup G]
    (htop : conjClosure L (pLayer G 2) = ⊤) : 2 ≤ CFSG.pRank 2 ↥(coreActionKernel L) := by
  obtain ⟨-, -, -, hlt, -⟩ := exists_component_of_counterexample hce
  obtain ⟨⟨-, -, ⟨ht, hLt, -⟩, -, -, -⟩, hcon⟩ := hce
  by_contra hrk
  have h1 : CFSG.pRank 2 ↥(coreActionKernel L) = 1 :=
    le_antisymm (by omega) (one_le_pRank_coreActionKernel ht hLt)
  apply hcon
  rw [htop] at hlt ⊢
  obtain ⟨eX⟩ := nonempty_quotient_top_equiv ht
  right; right; right; left
  refine ⟨eX.isSimpleGroup, ⟨fun e => ?_⟩, Or.inr (by rw [top_inf_eq]; exact h1)⟩
  have hcov := sup_oddCoreIn_eq_of_card_le (le_top : L ≤ ⊤) (Nat.card_congr e.toEquiv).le
  exact hlt.ne hcov

theorem footeInitialReductions_of_steps (h1 : FooteOddCoreReduction)
    (h2 : FooteComponentReduction) (h3 : FooteRankOneBranch) (h4 : FooteOuterReduction) :
    FooteInitialReductions := by
  intro G _ _ t L hmin hce
  have hO := h1 G t L hmin hce
  have hgen := h2 G t L hmin hce hO
  have hsimple₀ := isSimpleGroup_conjClosure_of_counterexample hce hO hgen
  have hr2 := h3 G t L hmin hce hO hgen hsimple₀
  have htop := h4 G t L hmin hce hO hgen hsimple₀ hr2
  have hGs : IsSimpleGroup G := by
    have h : IsSimpleGroup ↥(⊤ : Subgroup G) := htop ▸ hsimple₀
    exact (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.isSimpleGroup
  have hmax : FootePointedMaximal t L := hce.1.2.2.2.1
  exact ⟨hGs, hr2, L, ⟨⟨t, hmax⟩, ⟨MulEquiv.refl _⟩⟩,
    two_le_pRank_coreActionKernel_of_counterexample hce htop⟩

end CFSG.ComponentClassification.FooteLit
