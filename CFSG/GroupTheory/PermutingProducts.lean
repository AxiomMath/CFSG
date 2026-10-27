module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {G H : Type*} [Group G] [Group H]

theorem permutes_inf_of_le {B T N : Subgroup G} (hBN : B ≤ N)
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    (B : Set G) * ((T ⊓ N : Subgroup G) : Set G) =
      ((T ⊓ N : Subgroup G) : Set G) * (B : Set G) := by
  have h2 := Subgroup.inf_mul_assoc N T B hBN
  rw [inf_comm] at h2
  rw [Subgroup.mul_inf_assoc B T N hBN, h2, hperm, Set.inter_comm]

theorem map_permutes_map (f : G →* H) {B T : Subgroup G}
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    ((B.map f : Subgroup H) : Set H) * ((T.map f : Subgroup H) : Set H) =
      ((T.map f : Subgroup H) : Set H) * ((B.map f : Subgroup H) : Set H) := by
  simp only [Subgroup.coe_map]
  rw [← Set.image_mul f, hperm, Set.image_mul f]

end CFSG.GroupTheory

end
