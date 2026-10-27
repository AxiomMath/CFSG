module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

theorem sl23Pair_of_commuting {G : Type} [Group G] (K1 K2 : Subgroup G) (hcomm : ⁅K1, K2⁆ = ⊥)
    (e1 : Nonempty (↥K1 ≃* SL23)) (e2 : Nonempty (↥K2 ≃* SL23)) :
    SL23Pair ↥(K1 ⊔ K2) (K1.subgroupOf (K1 ⊔ K2)) (K2.subgroupOf (K1 ⊔ K2)) where
  comm a ha b hb := by
    have h1 : (a : G) ∈ Subgroup.centralizer (K2 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 b hb).symm
  top := codisjoint_iff.mp (Subgroup.codisjoint_subgroupOf_sup K1 K2)
  isoA := ⟨(Subgroup.subgroupOfEquivOfLe le_sup_left).trans e1.some⟩
  isoB := ⟨(Subgroup.subgroupOfEquivOfLe le_sup_right).trans e2.some⟩

end CFSG.OddStandard.SmallF3.Omega.K5
