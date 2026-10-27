module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open

variable {G : Type*} [Group G]

theorem componentLift_of_image (p : ℕ) (Y K : Subgroup G)
    (hKY : K ≤ Y) (hcore : lBalancePrimeCore p Y ≤ K)
    (himage : IsComponentOf (quotientImage p Y K) ⊤) :
    lBalanceIsComponentLift p Y K := by
  let q := QuotientGroup.mk' (pPrimeCore p Y)
  have hker : q.ker ≤ K.subgroupOf Y := by
    rw [QuotientGroup.ker_mk']
    intro k hk
    apply hcore
    rw [primeCore_eq_map]
    exact Subgroup.mem_map_of_mem Y.subtype hk
  have hchain : IsSubnormal K Y := by
    apply (subnormal_subgroupOf_iff hKY).mp
    have h := (Components.mathlib_subnormal_of_chain himage.2.1
      Subgroup.IsSubnormal.top).comap q
    change ((K.subgroupOf Y).map q).comap q |>.IsSubnormal at h
    rw [Subgroup.comap_map_eq_self hker] at h
    exact Components.chain_of_mathlib_subnormal h
  have hnormal : ((lBalancePrimeCore p Y).subgroupOf K).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hcore).mpr
    intro member actor hmember hactor
    exact (Subgroup.normal_subgroupOf_iff (primeCore_le p Y)).mp
      (primeCore_normal p Y) member actor hmember (hKY hactor)
  refine ⟨hcore, hchain, hnormal, ?_⟩
  let : ((lBalancePrimeCore p Y).subgroupOf K).Normal := hnormal
  exact Components.quasisimple_of_equiv
    (coreQuotientEquivImage p Y K hKY) himage.2.2

theorem pComponent_iff_minimal_image (p : ℕ) (Y L : Subgroup G) (hLY : L ≤ Y) :
    lBalanceIsPComponent p Y L ↔
      IsSubnormal L Y ∧ IsComponentOf (quotientImage p Y L) ⊤ ∧
      ∀ J : Subgroup G, J ≤ L → IsSubnormal J Y →
        quotientImage p Y J = quotientImage p Y L → J = L := by
  constructor
  · intro hL
    refine ⟨hL.1, pComponent_image p Y L hL, ?_⟩
    intro J hJL hJ hmap
    by_cases hLJ : L ≤ J
    · exact le_antisymm hJL hLJ
    · exact (hL.2.2 J ⟨hJL, hLJ⟩ hJ
        ((quotientImage_eq_iff p Y (hJL.trans hLY) hLY).mp hmap)).elim
  · rintro ⟨hchain, himage, hminimal⟩
    refine ⟨hchain, ?_, ?_⟩
    · apply componentLift_of_image p Y (L ⊔ lBalancePrimeCore p Y)
        (sup_le hLY (primeCore_le p Y)) le_sup_right
      rwa [quotientImage_sup_core p Y L hLY]
    · intro J hJL hJ hsup
      exact hJL.ne (hminimal J hJL.le hJ
        ((quotientImage_eq_iff p Y (hJL.le.trans hLY) hLY).mpr hsup))

theorem pComponent_exists_lift [Finite G] (p : ℕ) (Y : Subgroup G)
    (C : Subgroup (Y ⧸ pPrimeCore p Y)) (hC : IsComponentOf C ⊤) :
    ∃ L : Subgroup G, lBalanceIsPComponent p Y L ∧ quotientImage p Y L = C := by
  let q := QuotientGroup.mk' (pPrimeCore p Y)
  let : Group.IsPerfect C := ⟨hC.2.2.1⟩
  obtain ⟨L₀, hchain, hmap, _, hminimal⟩ := Components.perfect_subnormal_lift
    q (QuotientGroup.mk'_surjective _) C
    (Components.mathlib_subnormal_of_chain hC.2.1 Subgroup.IsSubnormal.top)
  let L := L₀.map Y.subtype
  have hLY : L ≤ Y := Subgroup.map_subtype_le _
  have hinternal : L.subgroupOf Y = L₀ :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have himage : quotientImage p Y L = C := by
    unfold quotientImage
    rw [hinternal]
    exact hmap
  refine ⟨L, ?_, himage⟩
  apply (pComponent_iff_minimal_image p Y L hLY).mpr
  refine ⟨(subnormal_subgroupOf_iff hLY).mp (hinternal.symm ▸ hchain), himage.symm ▸ hC, ?_⟩
  intro J hJL hJ hJmap
  have hJinternal : J.subgroupOf Y ≤ L₀ := by
    rw [← hinternal]
    exact fun _ hx => hJL hx
  have hJeq := hminimal (J.subgroupOf Y) hJinternal
    ((subnormal_subgroupOf_iff (hJL.trans hLY)).mpr hJ)
    (hJmap.trans himage)
  have h := congrArg (Subgroup.map Y.subtype) hJeq
  simpa only [Subgroup.map_subgroupOf_eq_of_le (hJL.trans hLY)] using h

end CFSG.ComponentClassification.LBalance
