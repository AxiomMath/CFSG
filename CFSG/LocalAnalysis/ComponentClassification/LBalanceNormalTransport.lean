module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceMinimalLifts
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def normalQuotientEquivImage (p : ℕ) [Fact p.Prime]
    (Y : Subgroup G) [Y.Normal] :
    (Y ⧸ pPrimeCore p Y) ≃* Y.map (QuotientGroup.mk' (pPrimeCore p G)) := by
  let q := QuotientGroup.mk' (pPrimeCore p G)
  let I := Y.map q
  let f : Y →* I := (q.comp Y.subtype).codRestrict I
    (fun y => Subgroup.mem_map_of_mem q y.property)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hker : pPrimeCore p Y = f.ker := by
    ext y
    have hcore : y ∈ pPrimeCore p Y ↔ y.val ∈ pPrimeCore p G := by
      rw [← primeCore_subgroupOf_eq p Y, primeCore_normal_intersection]
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, y.property, true_and]
    change y ∈ pPrimeCore p Y ↔ f y = 1
    rw [hcore, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact QuotientGroup.liftEquiv _ hsurj hker

theorem normalQuotientEquivImage_mk (p : ℕ) [Fact p.Prime]
    (Y : Subgroup G) [Y.Normal] (y : Y) :
    (normalQuotientEquivImage p Y ((QuotientGroup.mk' (pPrimeCore p Y)) y)).val =
      (QuotientGroup.mk' (pPrimeCore p G)) y.val := by
  dsimp only [normalQuotientEquivImage]
  erw [QuotientGroup.liftEquiv_mk]
  rfl

theorem quotientImage_normal_transport (p : ℕ) [Fact p.Prime]
    (Y L : Subgroup G) [Y.Normal] (hLY : L ≤ Y) :
    ((quotientImage p Y L).map (normalQuotientEquivImage p Y).toMonoidHom).map
        (Y.map (QuotientGroup.mk' (pPrimeCore p G))).subtype =
      L.map (QuotientGroup.mk' (pPrimeCore p G)) := by
  ext x
  constructor
  · rintro ⟨image, ⟨localImage, ⟨l, hl, rfl⟩, rfl⟩, rfl⟩
    exact Subgroup.mem_map.mpr ⟨l.val, hl, (normalQuotientEquivImage_mk p Y l).symm⟩
  · rintro ⟨l, hl, rfl⟩
    let y : Y := ⟨l, hLY hl⟩
    refine ⟨normalQuotientEquivImage p Y ((QuotientGroup.mk' (pPrimeCore p Y)) y),
      ⟨(QuotientGroup.mk' (pPrimeCore p Y)) y,
        Subgroup.mem_map_of_mem _ (show y ∈ L.subgroupOf Y from hl), rfl⟩, ?_⟩
    exact normalQuotientEquivImage_mk p Y y

theorem normal_pComponent_image (p : ℕ) [Fact p.Prime]
    (Y L : Subgroup G) [Y.Normal] (hL : lBalanceIsPComponent p Y L) :
    IsComponentOf (L.map (QuotientGroup.mk' (pPrimeCore p G))) ⊤ := by
  let q := QuotientGroup.mk' (pPrimeCore p G)
  let I := Y.map q
  let : I.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hI : IsSubnormal I ⊤ := Components.chain_of_mathlib_subnormal
    (inferInstance : I.Normal).isSubnormal
  have hC := (LocalComponents.equiv_iff (normalQuotientEquivImage p Y)
    (quotientImage p Y L)).mpr (pComponent_image p Y L hL)
  have h := LocalComponents.of_subnormal_subgroup I hI
    ((quotientImage p Y L).map (normalQuotientEquivImage p Y).toMonoidHom) hC
  rwa [quotientImage_normal_transport p Y L (subnormal_le hL.1)] at h

theorem normal_quotientImage_eq_iff (p : ℕ) [Fact p.Prime]
    (Y J L : Subgroup G) [Y.Normal] (hJY : J ≤ Y) (hLY : L ≤ Y) :
    quotientImage p Y J = quotientImage p Y L ↔
      J.map (QuotientGroup.mk' (pPrimeCore p G)) =
        L.map (QuotientGroup.mk' (pPrimeCore p G)) := by
  constructor
  · intro h
    rw [← quotientImage_normal_transport p Y J hJY,
      ← quotientImage_normal_transport p Y L hLY, h]
  · intro h
    rw [← quotientImage_normal_transport p Y J hJY,
      ← quotientImage_normal_transport p Y L hLY] at h
    exact Subgroup.map_injective (normalQuotientEquivImage p Y).injective
      (Subgroup.map_injective
        (Y.map (QuotientGroup.mk' (pPrimeCore p G))).subtype_injective h)

theorem pComponent_top_iff_minimal_image (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    lBalanceIsPComponent p ⊤ L ↔
      IsSubnormal L ⊤ ∧ IsComponentOf (L.map (QuotientGroup.mk' (pPrimeCore p G))) ⊤ ∧
      ∀ J : Subgroup G, J ≤ L → IsSubnormal J ⊤ →
        J.map (QuotientGroup.mk' (pPrimeCore p G)) =
          L.map (QuotientGroup.mk' (pPrimeCore p G)) → J = L := by
  constructor
  · intro hL
    refine ⟨hL.1, normal_pComponent_image p ⊤ L hL, ?_⟩
    intro J hJL hJ hmap
    exact ((pComponent_iff_minimal_image p ⊤ L le_top).mp hL).2.2 J hJL hJ
      ((normal_quotientImage_eq_iff p ⊤ J L le_top le_top).mpr hmap)
  · rintro ⟨hchain, hC, hminimal⟩
    apply (pComponent_iff_minimal_image p ⊤ L le_top).mpr
    refine ⟨hchain, ?_, ?_⟩
    · let q := QuotientGroup.mk' (pPrimeCore p G)
      let I := (⊤ : Subgroup G).map q
      have hI : IsComponentOf (L.map q |>.subgroupOf I) ⊤ :=
        LocalComponents.of_overgroup hC (Subgroup.map_mono le_top)
      have heq : (L.map q).subgroupOf I =
          (quotientImage p ⊤ L).map (normalQuotientEquivImage p ⊤).toMonoidHom := by
        have h := congrArg (Subgroup.comap I.subtype)
          (quotientImage_normal_transport p ⊤ L le_top)
        change (((quotientImage p ⊤ L).map
          (normalQuotientEquivImage p ⊤).toMonoidHom).map I.subtype).comap I.subtype =
          (L.map q).subgroupOf I at h
        rw [Subgroup.comap_map_eq_self_of_injective I.subtype_injective] at h
        exact h.symm
      rw [heq] at hI
      exact (LocalComponents.equiv_iff (normalQuotientEquivImage p ⊤)
        (quotientImage p ⊤ L)).mp hI
    · intro J hJL hJ hmap
      exact hminimal J hJL hJ
        ((normal_quotientImage_eq_iff p ⊤ J L le_top le_top).mp hmap)

theorem pComponent_normal_extension (p : ℕ) [Fact p.Prime]
    (Y L : Subgroup G) [Y.Normal] (hL : lBalanceIsPComponent p Y L) :
    lBalanceIsPComponent p ⊤ L := by
  apply (pComponent_top_iff_minimal_image p L).mpr
  refine ⟨?_, normal_pComponent_image p Y L hL, ?_⟩
  · have hY : IsSubnormal Y ⊤ := Components.chain_of_mathlib_subnormal
      (inferInstance : Y.Normal).isSubnormal
    have h := Components.mathlib_subnormal_of_chain hL.1
      (Components.mathlib_subnormal_of_chain hY Subgroup.IsSubnormal.top)
    exact Components.chain_of_mathlib_subnormal h
  · intro J hJL hJ hmap
    have hJY : J ≤ Y := hJL.trans (subnormal_le hL.1)
    have hJchain : IsSubnormal J Y := (subnormal_subgroupOf_iff hJY).mp (by
      simpa only [Subgroup.top_subgroupOf] using subnormal_subgroupOf hJ Y)
    exact ((pComponent_iff_minimal_image p Y L (subnormal_le hL.1)).mp hL).2.2
      J hJL hJchain ((normal_quotientImage_eq_iff p Y J L hJY (subnormal_le hL.1)).mpr hmap)

theorem pLayer_normal_mono (p : ℕ) [Fact p.Prime] (Y : Subgroup G) [Y.Normal] :
    lBalancePLayer p Y ≤ lBalancePLayer p ⊤ := by
  apply sSup_le
  intro L hL
  exact le_sSup (pComponent_normal_extension p Y L hL)

end CFSG.ComponentClassification.LBalance
