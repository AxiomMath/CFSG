module

public import CFSG.LocalAnalysis.ComponentClassification.LBalancePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open

variable {G : Type*} [Group G]

theorem subnormal_le {L Y : Subgroup G} (h : IsSubnormal L Y) : L ≤ Y :=
  h.le

theorem subnormal_subgroupOf {L K : Subgroup G} (h : IsSubnormal L K) (Y : Subgroup G) :
    IsSubnormal (L.subgroupOf Y) (K.subgroupOf Y) :=
  h.comap Y.subtype

theorem subnormal_subgroupOf_iff {L Y : Subgroup G} (hle : L ≤ Y) :
    IsSubnormal (L.subgroupOf Y) ⊤ ↔ IsSubnormal L Y := by
  constructor
  · intro h
    have hmapped := Components.chain_map Y.subtype h
    simpa only [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top,
      Subgroup.range_subtype] using hmapped
  · intro h
    simpa only [Subgroup.subgroupOf_self] using subnormal_subgroupOf h Y

@[expose] noncomputable def quotientImage (p : ℕ) (Y L : Subgroup G) :
    Subgroup (Y ⧸ pPrimeCore p Y) :=
  (L.subgroupOf Y).map (QuotientGroup.mk' (pPrimeCore p Y))

theorem quotientImage_sup_core (p : ℕ) (Y L : Subgroup G) (hL : L ≤ Y) :
    quotientImage p Y (L ⊔ lBalancePrimeCore p Y) = quotientImage p Y L := by
  have hsup : (L ⊔ lBalancePrimeCore p Y).subgroupOf Y =
      L.subgroupOf Y ⊔ pPrimeCore p Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (sup_le hL (primeCore_le p Y)),
      Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hL, ← primeCore_eq_map]
  unfold quotientImage
  rw [hsup, Subgroup.map_sup]
  have hbot : (pPrimeCore p Y).map (QuotientGroup.mk' (pPrimeCore p Y)) = ⊥ := by
    apply ((pPrimeCore p Y).map_eq_bot_iff).mpr
    rw [QuotientGroup.ker_mk']
  rw [hbot, sup_bot_eq]

theorem quotientImage_eq_iff (p : ℕ) (Y : Subgroup G) {J L : Subgroup G}
    (hJ : J ≤ Y) (hL : L ≤ Y) :
    quotientImage p Y J = quotientImage p Y L ↔
      J ⊔ lBalancePrimeCore p Y = L ⊔ lBalancePrimeCore p Y := by
  constructor
  · intro h
    have hc := congrArg (Subgroup.comap (QuotientGroup.mk' (pPrimeCore p Y))) h
    simp only [quotientImage, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hc
    have hm := congrArg (Subgroup.map Y.subtype) hc
    simpa only [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJ,
      Subgroup.map_subgroupOf_eq_of_le hL, ← primeCore_eq_map] using hm
  · intro h
    rw [← quotientImage_sup_core p Y J hJ, ← quotientImage_sup_core p Y L hL, h]

@[expose] noncomputable def coreQuotientEquivImage (p : ℕ) (Y K : Subgroup G)
    (hKY : K ≤ Y) [((lBalancePrimeCore p Y).subgroupOf K).Normal] :
    (K ⧸ (lBalancePrimeCore p Y).subgroupOf K) ≃* quotientImage p Y K := by
  let q := QuotientGroup.mk' (pPrimeCore p Y)
  let inclusion : K →* Y := Subgroup.inclusion hKY
  let f : K →* quotientImage p Y K :=
    (q.comp inclusion).codRestrict (quotientImage p Y K)
      (fun k => Subgroup.mem_map_of_mem q k.property)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp x.property
    exact ⟨⟨k.val, hk⟩, Subtype.ext hkx⟩
  have hker : (lBalancePrimeCore p Y).subgroupOf K = f.ker := by
    ext k
    have hcore : k.val ∈ lBalancePrimeCore p Y ↔ inclusion k ∈ pPrimeCore p Y := by
      rw [← primeCore_subgroupOf_eq p Y]
      rfl
    change k.val ∈ lBalancePrimeCore p Y ↔ f k = 1
    rw [hcore, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  exact QuotientGroup.liftEquiv _ hsurj hker

theorem componentLift_image (p : ℕ) (Y K : Subgroup G)
    (hK : lBalanceIsComponentLift p Y K) : IsComponentOf (quotientImage p Y K) ⊤ := by
  obtain ⟨hnormal, hquasi⟩ := hK.2.2
  let : ((lBalancePrimeCore p Y).subgroupOf K).Normal := hnormal
  refine ⟨le_top, ?_, ?_⟩
  · have hchain : IsSubnormal (K.subgroupOf Y) ⊤ :=
      (subnormal_subgroupOf_iff (subnormal_le hK.2.1)).mpr hK.2.1
    have hmapped := Components.chain_map (QuotientGroup.mk' (pPrimeCore p Y)) hchain
    simpa only [quotientImage,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hmapped
  · exact Components.quasisimple_of_equiv
      (coreQuotientEquivImage p Y K (subnormal_le hK.2.1)).symm hquasi

theorem pComponent_image (p : ℕ) (Y L : Subgroup G)
    (hL : lBalanceIsPComponent p Y L) : IsComponentOf (quotientImage p Y L) ⊤ := by
  have h := componentLift_image p Y (L ⊔ lBalancePrimeCore p Y) hL.2.1
  rwa [quotientImage_sup_core p Y L (subnormal_le hL.1)] at h

theorem pComponent_perfect (p : ℕ) (Y L : Subgroup G)
    (hL : lBalanceIsPComponent p Y L) : Group.IsPerfect L := by
  have himage := pComponent_image p Y L hL
  let : Group.IsPerfect (quotientImage p Y L) := ⟨himage.2.2.1⟩
  have hnormal : (⁅L, L⁆.subgroupOf L).Normal := by
    have h := (inferInstance : (⁅L, L⁆.subgroupOf (L ⊔ L)).Normal)
    rw [sup_idem] at h
    exact h
  have hchain : IsSubnormal ⁅L, L⁆ Y :=
    IsSubnormal.step (Subgroup.commutator_le_self L) hnormal hL.1
  have hderived : (⁅L, L⁆).subgroupOf Y = ⁅L.subgroupOf Y, L.subgroupOf Y⁆ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
        ((Subgroup.commutator_le_self L).trans (subnormal_le hL.1)),
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (subnormal_le hL.1)]
  have hmap : quotientImage p Y ⁅L, L⁆ = quotientImage p Y L := by
    unfold quotientImage
    rw [hderived, Subgroup.map_commutator]
    change ⁅quotientImage p Y L, quotientImage p Y L⁆ = quotientImage p Y L
    exact Subgroup.commutator_eq_self
  have hsup := (quotientImage_eq_iff p Y (subnormal_le hchain) (subnormal_le hL.1)).mp hmap
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self L)
  by_contra hle
  exact hL.2.2 ⁅L, L⁆ ⟨Subgroup.commutator_le_self L, hle⟩ hchain hsup

theorem pComponent_nontrivial (p : ℕ) (Y L : Subgroup G)
    (hL : lBalanceIsPComponent p Y L) : Nontrivial L := by
  have himage := pComponent_image p Y L hL
  let : Nontrivial (quotientImage p Y L) := Quasisimple.nontrivial himage.2.2
  let inclusion : L →* Y := Subgroup.inclusion (subnormal_le hL.1)
  let q := QuotientGroup.mk' (pPrimeCore p Y)
  let f : L →* quotientImage p Y L :=
    (q.comp inclusion).codRestrict (quotientImage p Y L)
      (fun l => Subgroup.mem_map_of_mem q l.property)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp x.property
    exact ⟨⟨l.val, hl⟩, Subtype.ext hlx⟩
  exact hsurj.nontrivial

theorem pLayer_perfect (p : ℕ) (Y : Subgroup G) : Group.IsPerfect (lBalancePLayer p Y) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _) _
  apply sSup_le
  intro L hL
  let : Group.IsPerfect L := pComponent_perfect p Y L hL
  rw [← Subgroup.commutator_eq_self (H := L)]
  exact Subgroup.commutator_mono (le_sSup hL) (le_sSup hL)

end CFSG.ComponentClassification.LBalance
