module

public import CFSG.Foundations.KCore
public import CFSG.Open.OrderForm

public section

universe u v

namespace CFSG.Open

theorem knownSimpleOrders_isoTransfer :
    KCore.IsoTransfer.{u, v} (fun S _ => Nat.card S ∈ knownSimpleOrders)
      (fun S _ => Nat.card S ∈ knownSimpleOrders) := fun e h => by
  show Nat.card _ ∈ knownSimpleOrders
  rw [← Nat.card_congr e.toEquiv]
  exact h

theorem knownSimpleOrders_isoInvariant :
    KCore.IsoInvariant.{u} (fun S _ => Nat.card S ∈ knownSimpleOrders) :=
  fun e h => knownSimpleOrders_isoTransfer e.symm h

theorem isCatalogGroup_isoTransfer :
    KCore.IsoTransfer.{u, v} @IsCatalogGroup @IsCatalogGroup :=
  fun e ⟨i, ⟨f⟩⟩ => ⟨i, ⟨e.symm.trans f⟩⟩

theorem isCatalogGroup_isoInvariant : KCore.IsoInvariant.{u} @IsCatalogGroup :=
  fun e h => isCatalogGroup_isoTransfer e.symm h

theorem isKProperByOrder_iff_kProperNonab {G : Type u} [Group G] :
    IsKProperByOrder G ↔ KCore.KProperNonab (fun S _ => Nat.card S ∈ knownSimpleOrders) G :=
  Iff.rfl

theorem IsKProperByOrder.of_surjective {G : Type u} {H : Type v} [Group G] [Group H]
    (hK : IsKProperByOrder G) (f : G →* H) (hf : Function.Surjective f) : IsKProperByOrder H := by
  intro K L hKt _ _ _ hn
  exact KCore.KProperNonab.catalogue_of_surjective_transfer knownSimpleOrders_isoTransfer hK
    (K.comap f) (KCore.comap_ne_top_of_surjective hf hKt) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp (f.subgroupComap K))
    ((QuotientGroup.mk'_surjective _).comp (f.subgroupComap_surjective K hf))

theorem IsKProperByOrder.of_injective {G : Type u} {H : Type v} [Group G] [Group H]
    (hK : IsKProperByOrder H) (f : G →* H) (hf : Function.Injective f) : IsKProperByOrder G := by
  intro K L hKt _ _ _ hn
  let e : K ≃* K.map f := K.equivMapOfInjective f hf
  exact KCore.KProperNonab.catalogue_of_surjective_transfer knownSimpleOrders_isoTransfer hK
    (K.map f) (KCore.map_ne_top_of_injective hf hKt) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)

namespace IsKGroup

variable {X : Type u} {Y : Type v} [Group X] [Group Y]

theorem isCatalogGroup_of_surjective (hX : IsKGroup X) (K : Subgroup X) {S : Type v} [Group S]
    [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S)
    (hφ : Function.Surjective φ) : IsCatalogGroup S :=
  KCore.KGroupNonab.catalogue_of_surjective_transfer isCatalogGroup_isoTransfer hX K hnonab φ hφ

theorem of_surjective (hX : IsKGroup X) (f : X →* Y) (hf : Function.Surjective f) :
    IsKGroup Y :=
  KCore.KGroupNonab.of_surjective_transfer isCatalogGroup_isoTransfer hX f hf

theorem of_injective (hY : IsKGroup Y) (f : X →* Y) (hf : Function.Injective f) :
    IsKGroup X := by
  intro K L _ _ _ hn
  let e : K ≃* K.map f := K.equivMapOfInjective f hf
  exact hY.isCatalogGroup_of_surjective (K.map f) hn
    ((QuotientGroup.mk' (L.subgroupOf K)).comp e.symm.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp e.symm.surjective)

theorem subgroup (hX : IsKGroup X) (H : Subgroup X) : IsKGroup H :=
  KCore.KGroupNonab.subgroup isCatalogGroup_isoInvariant hX H

theorem quotient (hX : IsKGroup X) (M : Subgroup X) [M.Normal] : IsKGroup (X ⧸ M) :=
  KCore.KGroupNonab.quotient isCatalogGroup_isoInvariant hX M

theorem of_le {G : Type u} [Group G] {H L : Subgroup G} (hH : IsKGroup H) (hLH : L ≤ H) :
    IsKGroup L :=
  hH.of_injective (Subgroup.inclusion hLH) (Subgroup.inclusion_injective hLH)

end IsKGroup

theorem IsKProper.isKGroup {G : Type u} [Group G] (hG : IsKProper G) (H : Subgroup G)
    (hH : H ≠ ⊤) : IsKGroup H :=
  KCore.KProperNonab.kGroupNonab isCatalogGroup_isoInvariant hG H hH

end CFSG.Open
