module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G]

theorem IsSylowOf.inf_of_isSubnormal {p : ℕ} [Fact p.Prime] {S K L : Subgroup G}
    (hS : IsSylowOf p S L) (hKL : CFSG.Open.IsSubnormal K L) :
    IsSylowOf p (S ⊓ K) K := by
  induction hKL generalizing S with
  | refl H =>
      rwa [inf_eq_left.mpr hS.le]
  | @step H M L hHM hNorm hML ih =>
      have hM : IsSylowOf p (S ⊓ M) M := ih hS
      have hnorm : M ≤ Subgroup.normalizer (H : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hNorm
      have h := hM.inf_of_le_normalizer hHM hnorm
      rwa [inf_assoc, inf_eq_right.mpr hHM] at h

end CFSG.ABGLocalTools

