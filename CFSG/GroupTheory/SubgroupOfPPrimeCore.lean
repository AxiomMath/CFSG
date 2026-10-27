module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PCore.CommutingBalance

public section

namespace CFSG.GroupTheory

theorem subgroupOf_inSubgroup_pPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K Y : Subgroup G} (hKY : K ≤ Y)
    (hYK : Y ≤ Subgroup.normalizer (K : Set G)) :
    (inSubgroup (pPrimeCore p) Y).subgroupOf K = pPrimeCore p ↥K := by
  have hN : (K.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYK
  have h1 := congrArg (Subgroup.map Y.subtype)
    (CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := p) hN)
  rw [CFSG.pPrimeCore_map_subgroupOf p K Y hKY,
    Subgroup.map_inf _ _ _ Y.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hKY] at h1
  change ((pPrimeCore p ↥Y).map Y.subtype).subgroupOf K = pPrimeCore p ↥K
  rw [← Subgroup.inf_subgroupOf_left ((pPrimeCore p ↥Y).map Y.subtype) K, ← h1,
    Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

end CFSG.GroupTheory
