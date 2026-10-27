
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

theorem commutator_subgroupOf_self {G : Type} [Group G] {K L : Subgroup G} (hLK : L ≤ K) :
    ⁅L.subgroupOf K, L.subgroupOf K⁆ = (⁅L, L⁆).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  have hc : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact K.mul_mem (K.mul_mem (K.mul_mem (hLK ha) (hLK hb)) (K.inv_mem (hLK ha)))
      (K.inv_mem (hLK hb))
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hLK,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hc]

end CFSG.QuasithinUnique.A5
