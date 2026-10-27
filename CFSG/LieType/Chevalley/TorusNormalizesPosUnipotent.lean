module

public import CFSG.LieType.Chevalley.ChevalleySplitBN

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem torusSub_le_normalizer_posUnipotentSub {τ : Tag} {K : Type} [Field K] :
    torusSub τ K ≤
      Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K)) := by
  intro x hx
  have hxN := torusGroup_le_normalizer_posUnipotent (τ := τ) (R := K)
    (Subgroup.mem_subgroupOf.mp hx)
  rw [Subgroup.mem_normalizer_iff] at hxN ⊢
  intro y
  simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
    Subgroup.coe_inv] using hxN y

end CFSG.LieType.Chevalley
