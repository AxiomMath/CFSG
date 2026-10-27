module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

namespace CFSG.Adapters

open CFSG.Open in
theorem isSubnormal_top_iff {G : Type*} [Group G] (H : Subgroup G) :
    IsSubnormal H ⊤ ↔ H.IsSubnormal :=
  IsSubnormal.top_iff

theorem isComponentOf_top_iff {G : Type*} [Group G] (L : Subgroup G) :
    CFSG.Open.IsComponentOf L ⊤ ↔
      CFSG.GorensteinWalter.IsComponentOf L ⊤ := by
  unfold CFSG.Open.IsComponentOf
    CFSG.GorensteinWalter.IsComponentOf
  rw [isSubnormal_top_iff]
  have hsn : L.IsSubnormal ↔ (L.subgroupOf ⊤).IsSubnormal :=
    ⟨fun h => h.subgroupOf, fun h => Subgroup.IsSubnormal.trans le_top h Subgroup.IsSubnormal.top⟩
  have hqs : CFSG.Open.IsQuasisimple L ↔
      CFSG.GorensteinWalter.IsQuasisimple L := by
    unfold CFSG.Open.IsQuasisimple
      CFSG.GorensteinWalter.IsQuasisimple
    refine ⟨fun ⟨h1, h2⟩ => ⟨?_, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩
    obtain ⟨a, b, hab⟩ := h2.exists_pair_ne
    refine ⟨?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [h])⟩
  rw [hsn, hqs]

theorem componentLayerOf_top_eq_componentClassification (G : Type*) [Group G] :
    CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup G) =
      CFSG.ComponentClassification.Layer.subgroup G := by
  unfold CFSG.GorensteinWalter.componentLayerOf; simp only [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
  congr 1
  ext L
  exact (isComponentOf_top_iff L).symm

theorem fittingSubgroupOf_top_eq_foundations (G : Type*) [Group G] [Finite G] :
    CFSG.fittingSubgroupOf (⊤ : Subgroup G) = CFSG.fittingSubgroup G :=
  le_antisymm (CFSG.fittingSubgroupOf_le_fittingSubgroup ⊤ Subgroup.normal_top)
    (CFSG.le_fittingSubgroupOf_of_normal_nilpotent le_top inferInstance inferInstance)

theorem fittingSubgroupOf_top_eq_componentClassification (G : Type*) [Group G] [Finite G] :
    CFSG.fittingSubgroupOf (⊤ : Subgroup G) = CFSG.ComponentClassification.Fitting.subgroup G :=
  fittingSubgroupOf_top_eq_foundations G

theorem generalizedFittingSubgroupOf_top_eq_componentClassification (G : Type*) [Group G]
    [Finite G] :
    CFSG.GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup G) =
      CFSG.ComponentClassification.GeneralizedFitting.subgroup G := by
  change CFSG.fittingSubgroupOf (⊤ : Subgroup G) ⊔
      CFSG.GorensteinWalter.componentLayerOf (⊤ : Subgroup G) = _
  rw [fittingSubgroupOf_top_eq_componentClassification,
    componentLayerOf_top_eq_componentClassification]
  rfl

end CFSG.Adapters
