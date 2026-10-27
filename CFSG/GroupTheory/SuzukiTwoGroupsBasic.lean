module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega

public section

namespace CFSG.GroupTheory

open Subgroup

@[expose] def IsSuzukiTwoGroup (S : Type*) [Group S] : Prop :=
  Finite S ∧ IsPGroup 2 S ∧ ¬ IsMulCommutative S ∧
    (∃ x y : S, orderOf x = 2 ∧ orderOf y = 2 ∧ x ≠ y) ∧
    ∃ A : Subgroup (MulAut S), IsCyclic A ∧
      ∀ x y : S, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a x = y

namespace SuzukiTwoGroup

variable {S : Type*} [Group S]

@[expose] def IsStable (A : Subgroup (MulAut S)) (T : Subgroup S) : Prop :=
  ∀ a ∈ A, ∀ t ∈ T, a t ∈ T

theorem apply_mem_center (a : MulAut S) {z : S} (hz : z ∈ center S) : a z ∈ center S := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h := Subgroup.mem_center_iff.1 hz (a.symm g)
  calc g * a z = a (a.symm g * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = a (z * a.symm g) := by rw [h]
    _ = a z * g := by rw [map_mul, MulEquiv.apply_symm_apply]

theorem orderOf_eq_two_iff_sq_eq_one {x : S} : orderOf x = 2 ↔ x ^ 2 = 1 ∧ x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_iff

theorem exists_orderOf_eq_two [Finite S] (hS : IsPGroup 2 S) [Nontrivial S] :
    ∃ x : S, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card).ne'
  exact exists_prime_orderOf_dvd_card' 2 (hk ▸ dvd_pow_self 2 hk0)

theorem exists_mem_orderOf_eq_two [Finite S] (hS : IsPGroup 2 S) {T : Subgroup S}
    (hT : T ≠ ⊥) : ∃ t ∈ T, orderOf t = 2 := by
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT
  obtain ⟨t, ht⟩ := exists_orderOf_eq_two (hS.to_subgroup T)
  exact ⟨t, t.2, by rwa [Subgroup.orderOf_coe]⟩

variable [Finite S] (hS : IsPGroup 2 S) {A : Subgroup (MulAut S)}
  (htrans : ∀ x y : S, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a x = y)
include hS htrans

theorem mem_center_of_orderOf_eq_two {x : S} (hx : orderOf x = 2) : x ∈ center S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := ⟨⟨x, 1, fun h => by rw [h, orderOf_one] at hx; norm_num at hx⟩⟩
  obtain ⟨z, hz, hz2⟩ := exists_mem_orderOf_eq_two hS (T := center S)
    (ne_of_gt hS.bot_lt_center)
  obtain ⟨a, -, rfl⟩ := htrans z x hz2 hx
  exact apply_mem_center a hz

omit [Finite S] hS htrans in
theorem mem_omega₁_iff_of_forall {x : S} (h : ∀ y : S, y ^ 2 = 1 → y ∈ center S) :
    x ∈ omega₁ S (p := 2) ↔ x ^ 2 = 1 := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (fun y hy => ?_) (one_pow 2) (fun y z _ _ hy hz => ?_)
      (fun y _ hy => ?_) hx
    · simpa using hy
    · have hc : Commute y z := ((Subgroup.mem_center_iff.1 (h y hy)) z).symm
      rw [hc.mul_pow, hy, hz, one_mul]
    · rw [inv_pow, hy, inv_one]
  · intro hx
    exact Subgroup.subset_closure (by simpa using hx)

theorem mem_omega₁_iff {x : S} : x ∈ omega₁ S (p := 2) ↔ x ^ 2 = 1 := by
  refine mem_omega₁_iff_of_forall fun y hy => ?_
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  · exact mem_center_of_orderOf_eq_two hS htrans (orderOf_eq_two_iff_sq_eq_one.2 ⟨hy, hy1⟩)

theorem omega₁_le_center : omega₁ S (p := 2) ≤ center S := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  · exact mem_center_of_orderOf_eq_two hS htrans
      (orderOf_eq_two_iff_sq_eq_one.2 ⟨(mem_omega₁_iff hS htrans).1 hx, hx1⟩)

theorem omega₁_le_of_isStable {T : Subgroup S} (hT : T ≠ ⊥) (hTA : IsStable A T) :
    omega₁ S (p := 2) ≤ T := by
  obtain ⟨t, ht, ht2⟩ := exists_mem_orderOf_eq_two hS hT
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  · obtain ⟨a, ha, rfl⟩ := htrans t x ht2
      (orderOf_eq_two_iff_sq_eq_one.2 ⟨(mem_omega₁_iff hS htrans).1 hx, hx1⟩)
    exact hTA a ha t ht

end SuzukiTwoGroup

end CFSG.GroupTheory
