module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.GroupTheory

theorem mem_closure_pair_iff_of_commute {G : Type*} [Group G] {x y z : G}
    (hxy : Commute x y) :
    z ∈ Subgroup.closure ({x, y} : Set G) ↔ ∃ m n : ℤ, x ^ m * y ^ n = z := by
  have hmul : ∀ m n p q : ℤ, x ^ (m + p) * y ^ (n + q) = x ^ m * y ^ n * (x ^ p * y ^ q) := by
    intro m n p q
    rw [mul_assoc, ← mul_assoc (y ^ n) (x ^ p) (y ^ q), (hxy.symm.zpow_zpow n p).eq,
      mul_assoc (x ^ p) (y ^ n) (y ^ q), ← mul_assoc (x ^ m) (x ^ p) (y ^ n * y ^ q),
      ← zpow_add, ← zpow_add]
  constructor
  · intro hz
    let S : Subgroup G :=
      { carrier := {z | ∃ m n : ℤ, x ^ m * y ^ n = z}
        one_mem' := ⟨0, 0, by simp⟩
        mul_mem' := by
          rintro a b ⟨m, n, rfl⟩ ⟨p, q, rfl⟩
          exact ⟨m + p, n + q, hmul m n p q⟩
        inv_mem' := by
          rintro a ⟨m, n, rfl⟩
          refine ⟨-m, -n, ?_⟩
          rw [mul_inv_rev, zpow_neg, zpow_neg]
          exact ((hxy.zpow_zpow m n).inv_inv).eq }
    exact (Subgroup.closure_le S).mpr (by
      intro w hw
      rcases hw with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩) hz
  · rintro ⟨m, n, rfl⟩
    exact mul_mem
      (Subgroup.zpow_mem (K := Subgroup.closure ({x, y} : Set G))
        (Subgroup.subset_closure (by simp)) m)
      (Subgroup.zpow_mem (K := Subgroup.closure ({x, y} : Set G))
        (Subgroup.subset_closure (by simp)) n)

end CFSG.GroupTheory
