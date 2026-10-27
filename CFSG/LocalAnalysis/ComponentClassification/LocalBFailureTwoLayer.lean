module

public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.PComponentCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public section

namespace CFSG.ComponentClassification.LocalBFailure

theorem pLayer_two_eq_twoLayer (G : Type*) [Group G] :
    CFSG.pLayer G 2 = TwoLayer.subgroup G := by
  unfold CFSG.pLayer TwoLayer.subgroup
  congr 1
  ext L
  exact CatalogueBAlternating.pComponent_two_iff L

theorem badSubgroup_eq_badTwoComponentSubgroup (G : Type*) [Group G] :
    TwoComponents.badSubgroup G = CatalogueBPrimeJoin.badTwoComponentSubgroup G := by
  unfold TwoComponents.badSubgroup CatalogueBPrimeJoin.badTwoComponentSubgroup
  congr 1
  ext L
  exact and_congr (CatalogueBAlternating.pComponent_two_iff L).symm
    (not_congr CatalogueBAlternating.quasisimple_iff_native.symm)

theorem local_two_layer_component_ordinary_layer_or_bad {G : Type*} [Group G] [Finite G]
    (x : G) (L : Subgroup (Subgroup.centralizer ({x} : Set G))) (hL : CFSG.IsPComponent 2 L)
    (hle : L.map (Subgroup.centralizer ({x} : Set G)).subtype ≤ CFSG.pLayer G 2) :
    L.map (Subgroup.centralizer ({x} : Set G)).subtype ≤ CFSG.layer G ∨
      L.map (Subgroup.centralizer ({x} : Set G)).subtype ≤ TwoComponents.badSubgroup G := by
  rw [CFSG.layer_eq_componentClassification]
  rw [pLayer_two_eq_twoLayer] at hle
  exact TwoLayer.local_component_in_layer_or_bad x L
    ((CatalogueBAlternating.pComponent_two_iff L).mp hL) hle

end CFSG.ComponentClassification.LocalBFailure
