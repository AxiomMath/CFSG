module

public import CFSG.CGT.PushingUpLit.EightOneRel

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel
open scoped commutatorElement

section Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_commutator_eq {A B K : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) :
    ⁅A.subgroupOf K, B.subgroupOf K⁆ = ⁅A, B⁆.subgroupOf K := by
  have hAB : ⁅A, B⁆ ≤ K := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hA ha) (hB hb)) (K.inv_mem (hA ha)))
      (K.inv_mem (hB hb))
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hAB]

omit [Finite G] in
theorem isSylowOf_subgroupOf_iff' {S X K : Subgroup G} (hS : S ≤ K) (hX : X ≤ K) :
    IsSylowOf 2 (S.subgroupOf K) (X.subgroupOf K) ↔ IsSylowOf 2 S X := by
  rw [← Sec9B.isSylowOf_map_iff (f := K.subtype) K.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hS, Subgroup.map_subgroupOf_eq_of_le hX]

open CFSG.Assembly (KProper InCatalog)

end Subgroup

end CFSG.CGT.PushingUpLit.Glue
