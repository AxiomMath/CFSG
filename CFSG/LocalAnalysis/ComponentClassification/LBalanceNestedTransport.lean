module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceNormalTransport

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] noncomputable def nestedQuotientEquiv (p : ℕ) (Y H : Subgroup G) (hYH : Y ≤ H) :
    ((Y.subgroupOf H) ⧸ pPrimeCore p (Y.subgroupOf H)) ≃* (Y ⧸ pPrimeCore p Y) :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hYH)
    (pPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hYH))

theorem nestedQuotientEquiv_mk (p : ℕ) (Y H : Subgroup G) (hYH : Y ≤ H)
    (y : Y.subgroupOf H) :
    nestedQuotientEquiv p Y H hYH ((QuotientGroup.mk' (pPrimeCore p (Y.subgroupOf H))) y) =
      (QuotientGroup.mk' (pPrimeCore p Y)) (Subgroup.subgroupOfEquivOfLe hYH y) := by
  exact QuotientGroup.congr_mk' _ _ _ _ y

theorem quotientImage_nested_map (p : ℕ) (Y H : Subgroup G) (hYH : Y ≤ H)
    (J : Subgroup H) (hJY : J ≤ Y.subgroupOf H) :
    (quotientImage p (Y.subgroupOf H) J).map (nestedQuotientEquiv p Y H hYH).toMonoidHom =
      quotientImage p Y (J.map H.subtype) := by
  ext x
  constructor
  · rintro ⟨image, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨Subgroup.subgroupOfEquivOfLe hYH j, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem H.subtype hj
    · exact (nestedQuotientEquiv_mk p Y H hYH j).symm
  · rintro ⟨y, ⟨j, hj, hjy⟩, rfl⟩
    let j' : Y.subgroupOf H := ⟨j, hJY hj⟩
    refine ⟨(QuotientGroup.mk' (pPrimeCore p (Y.subgroupOf H))) j',
      Subgroup.mem_map_of_mem _ (show j' ∈ J.subgroupOf (Y.subgroupOf H) from hj), ?_⟩
    change nestedQuotientEquiv p Y H hYH
      ((QuotientGroup.mk' (pPrimeCore p (Y.subgroupOf H))) j') = _
    rw [nestedQuotientEquiv_mk]
    exact congrArg (QuotientGroup.mk' (pPrimeCore p Y)) (Subtype.ext hjy)

theorem quotientImage_nested_subgroupOf (p : ℕ) (Y H L : Subgroup G)
    (hYH : Y ≤ H) (hLY : L ≤ Y) :
    (quotientImage p (Y.subgroupOf H) (L.subgroupOf H)).map
        (nestedQuotientEquiv p Y H hYH).toMonoidHom = quotientImage p Y L := by
  have h := quotientImage_nested_map p Y H hYH (L.subgroupOf H) (fun _ hx => hLY hx)
  rwa [Subgroup.map_subgroupOf_eq_of_le (hLY.trans hYH)] at h

theorem pComponent_nested_iff (p : ℕ) (Y H L : Subgroup G)
    (hYH : Y ≤ H) (hLY : L ≤ Y) :
    lBalanceIsPComponent p (Y.subgroupOf H) (L.subgroupOf H) ↔
      lBalanceIsPComponent p Y L := by
  have hLinternal : L.subgroupOf H ≤ Y.subgroupOf H := fun _ hx => hLY hx
  constructor
  · intro hL
    obtain ⟨hchain, himage, hminimal⟩ :=
      (pComponent_iff_minimal_image p (Y.subgroupOf H) (L.subgroupOf H) hLinternal).mp hL
    apply (pComponent_iff_minimal_image p Y L hLY).mpr
    refine ⟨?_, ?_, ?_⟩
    · have h := Components.chain_map H.subtype hchain
      simpa only [Subgroup.map_subgroupOf_eq_of_le (hLY.trans hYH),
        Subgroup.map_subgroupOf_eq_of_le hYH] using h
    · have h := (LocalComponents.equiv_iff (nestedQuotientEquiv p Y H hYH)
        (quotientImage p (Y.subgroupOf H) (L.subgroupOf H))).mpr himage
      rwa [quotientImage_nested_subgroupOf p Y H L hYH hLY] at h
    · intro J hJL hJ hmap
      have hJinternal : J.subgroupOf H ≤ L.subgroupOf H := fun _ hx => hJL hx
      have hJmap : quotientImage p (Y.subgroupOf H) (J.subgroupOf H) =
          quotientImage p (Y.subgroupOf H) (L.subgroupOf H) := by
        apply Subgroup.map_injective (nestedQuotientEquiv p Y H hYH).injective
        change (quotientImage p (Y.subgroupOf H) (J.subgroupOf H)).map
            (nestedQuotientEquiv p Y H hYH).toMonoidHom =
          (quotientImage p (Y.subgroupOf H) (L.subgroupOf H)).map
            (nestedQuotientEquiv p Y H hYH).toMonoidHom
        rw [quotientImage_nested_subgroupOf p Y H J hYH (hJL.trans hLY),
          quotientImage_nested_subgroupOf p Y H L hYH hLY]
        exact hmap
      have heq := hminimal (J.subgroupOf H) hJinternal (subnormal_subgroupOf hJ H) hJmap
      have h := congrArg (Subgroup.map H.subtype) heq
      simpa only [Subgroup.map_subgroupOf_eq_of_le (hJL.trans (hLY.trans hYH)),
        Subgroup.map_subgroupOf_eq_of_le (hLY.trans hYH)] using h
  · intro hL
    obtain ⟨hchain, himage, hminimal⟩ := (pComponent_iff_minimal_image p Y L hLY).mp hL
    apply (pComponent_iff_minimal_image p (Y.subgroupOf H) (L.subgroupOf H) hLinternal).mpr
    refine ⟨subnormal_subgroupOf hchain H, ?_, ?_⟩
    · apply (LocalComponents.equiv_iff (nestedQuotientEquiv p Y H hYH)
        (quotientImage p (Y.subgroupOf H) (L.subgroupOf H))).mp
      rwa [quotientImage_nested_subgroupOf p Y H L hYH hLY]
    · intro J hJL hJ hmap
      have hJY : J ≤ Y.subgroupOf H := hJL.trans hLinternal
      have hJG : J.map H.subtype ≤ L := by
        rintro x ⟨j, hj, rfl⟩
        exact hJL hj
      have hJGchain : IsSubnormal (J.map H.subtype) Y := by
        have h := Components.chain_map H.subtype hJ
        simpa only [Subgroup.map_subgroupOf_eq_of_le hYH] using h
      have hJGmap := congrArg (Subgroup.map (nestedQuotientEquiv p Y H hYH).toMonoidHom) hmap
      rw [quotientImage_nested_map p Y H hYH J hJY,
        quotientImage_nested_subgroupOf p Y H L hYH hLY] at hJGmap
      have heq := hminimal (J.map H.subtype) hJG hJGchain hJGmap
      apply Subgroup.map_injective H.subtype_injective
      rwa [Subgroup.map_subgroupOf_eq_of_le (hLY.trans hYH)]

theorem pLayer_nested_map (p : ℕ) (Y H : Subgroup G) (hYH : Y ≤ H) :
    (lBalancePLayer p (Y.subgroupOf H)).map H.subtype = lBalancePLayer p Y := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro L hL
    have hLY := subnormal_le hL.1
    have hmapY : L.map H.subtype ≤ Y := by
      rintro x ⟨l, hl, rfl⟩
      exact hLY hl
    have hinternal : (L.map H.subtype).subgroupOf H = L :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hcomponent := (pComponent_nested_iff p Y H (L.map H.subtype) hYH hmapY).mp
      (hinternal.symm ▸ hL)
    exact Subgroup.map_le_iff_le_comap.mp (le_sSup hcomponent)
  · apply sSup_le
    intro L hL
    have hLY := subnormal_le hL.1
    have hinternal := (pComponent_nested_iff p Y H L hYH hLY).mpr hL
    have hle := Subgroup.map_mono (f := H.subtype)
      (show L.subgroupOf H ≤ lBalancePLayer p (Y.subgroupOf H) from le_sSup hinternal)
    simpa only [Subgroup.map_subgroupOf_eq_of_le (hLY.trans hYH)] using hle

theorem pLayer_relative_normal_mono [Finite G] (p : ℕ) [Fact p.Prime]
    (Y H : Subgroup G) (hYH : Y ≤ H) [(Y.subgroupOf H).Normal] :
    lBalancePLayer p Y ≤ lBalancePLayer p H := by
  have h := Subgroup.map_mono (f := H.subtype) (pLayer_normal_mono p (Y.subgroupOf H))
  have htop := pLayer_nested_map p H H le_rfl
  rw [Subgroup.subgroupOf_self] at htop
  rwa [pLayer_nested_map p Y H hYH, htop] at h

theorem pLayer_centralizer_le_normalizer [Finite G] (p : ℕ) [Fact p.Prime] (P : Subgroup G) :
    lBalancePLayer p (Subgroup.centralizer (P : Set G)) ≤
      lBalancePLayer p (Subgroup.normalizer (P : Set G)) :=
  pLayer_relative_normal_mono p _ _ (Subgroup.centralizer_le_normalizer _)

end CFSG.ComponentClassification.LBalance
