module

public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec5g8_card_map {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G)))
    {W : Subgroup G} (hWH : W ≤ centralizer ({z} : Set G)) (hzW : z ∈ W) :
    Nat.card ↥((W.subgroupOf (centralizer ({z} : Set G))).map π) * 2 = Nat.card ↥W := by
  let H := centralizer ({z} : Set G)
  have hmain := Subgroup.card_ker_mul_card_range (π.domRestrict (W.subgroupOf H))
  rw [MonoidHom.domRestrict_range] at hmain
  have hcardW : Nat.card ↥(W.subgroupOf H) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv
  rw [hcardW] at hmain
  have hker2 : Nat.card (π.domRestrict (W.subgroupOf H)).ker = 2 := by
    have hinj : Function.Injective (H.subtype.comp (W.subgroupOf H).subtype) :=
      H.subtype_injective.comp Subtype.val_injective
    have himg : (π.domRestrict (W.subgroupOf H)).ker.map
        (H.subtype.comp (W.subgroupOf H).subtype) = zpowers z := by
      ext w
      constructor
      · rintro ⟨c, hc, rfl⟩
        have h2 : (c : ↥H) ∈ π.ker := hc
        rw [hker] at h2
        exact Subgroup.mem_subgroupOf.mp h2
      · intro hw
        have hwW : w ∈ W := (Subgroup.zpowers_le.mpr hzW) hw
        have hwH : w ∈ H := hWH hwW
        refine ⟨⟨⟨w, hwH⟩, Subgroup.mem_subgroupOf.mpr hwW⟩, ?_, rfl⟩
        show π ⟨w, hwH⟩ = 1
        have h2 : (⟨w, hwH⟩ : ↥H) ∈ π.ker := by
          rw [hker]
          exact Subgroup.mem_subgroupOf.mpr hw
        exact h2
    rw [← Subgroup.card_map_of_injective hinj, himg, Nat.card_zpowers, hz]
  rw [hker2] at hmain
  change 2 * Nat.card ↥((W.subgroupOf (centralizer ({z} : Set G))).map π) = Nat.card ↥W at hmain
  omega

end CFSG.OddStandard.SmallF3.Omega
