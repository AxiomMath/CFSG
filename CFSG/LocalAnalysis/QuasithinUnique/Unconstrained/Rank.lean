module

public import CFSG.GroupTheory.ABGDGroups.LinearSemidihedral

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem dihedral_card_le_four {m : ℕ} (hm : 1 ≤ m) (W : Subgroup (DihedralGroup (2 ^ m)))
    (hW : ∀ w ∈ W, w ^ 2 = 1) : Nat.card W ≤ 4 := by
  rcases CFSG.GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm W with
    hcyc | ⟨k, hk, ⟨eW⟩⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
    have hcard : Nat.card W = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have hg2 : orderOf g ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hW _ g.property))
    have := Nat.le_of_dvd (by norm_num) hg2
    omega
  · have hr : orderOf (eW.symm (DihedralGroup.r 1)) = 2 ^ k := by
      rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hr2 : 2 ^ k ∣ 2 := by
      rw [← hr]
      exact orderOf_dvd_of_pow_eq_one
        (Subtype.ext (by simpa using hW _ (eW.symm (DihedralGroup.r 1)).property))
    have hk1 : k ≤ 1 := by
      have := Nat.le_of_dvd (by norm_num) hr2
      by_contra hk2
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.card_congr eW.toEquiv, DihedralGroup.nat_card]
    obtain rfl : k = 1 := by omega
    norm_num

section Transport

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem natCard_map_subgroupOf {X E : Subgroup G} (hEX : E ≤ X) {Y : Type*} [Group Y]
    (e : ↥X ≃* Y) : Nat.card ((E.subgroupOf X).map e.toMonoidHom) = Nat.card E := by
  rw [Subgroup.card_map_of_injective e.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv

theorem card_le_four_of_dihedral {n : ℕ} {X : Subgroup G} (hX2 : IsPGroup 2 X) (hn : 2 ≤ n)
    (e : ↥X ≃* DihedralGroup n) {E : Subgroup G} (hEX : E ≤ X) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hX2.exists_card_eq
  have hcard : Nat.card X = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hn2 : 2 * n = 2 ^ j := by rw [← hcard, hj]
  have hj1 : 1 ≤ j := by
    by_contra hcon
    have : j = 0 := by omega
    subst this
    omega
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 ^ m := ⟨j - 1, by omega⟩
  have hm : 1 ≤ m := by
    by_contra hcon
    have : m = 0 := by omega
    subst this
    omega
  rw [← natCard_map_subgroupOf hEX e]
  refine dihedral_card_le_four hm _ ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, ← map_pow]
  have : x ^ 2 = 1 := Subtype.ext (by simpa using hE _ hx)
  rw [this, map_one]

omit [Finite G] in
theorem card_le_four_of_semidihedral {X : Subgroup G} (e : ↥X ≃* SemidihedralGroup 4)
    {E : Subgroup G} (hEX : E ≤ X) (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  rw [← natCard_map_subgroupOf hEX e]
  refine CFSG.ABGDGroups.semidihedral_card_le_four (le_refl 4) _ ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, ← map_pow]
  have : x ^ 2 = 1 := Subtype.ext (by simpa using hE _ hx)
  rw [this, map_one]

@[expose] def IsDihedralOrSemidihedralShape (X : Subgroup G) : Prop :=
  (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥X ≃* DihedralGroup n)) ∨ Nonempty (↥X ≃* SemidihedralGroup 4)

theorem card_le_four_of_shape {X : Subgroup G} (hX2 : IsPGroup 2 X)
    (hshape : IsDihedralOrSemidihedralShape X) {E : Subgroup G} (hEX : E ≤ X)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  rcases hshape with ⟨n, hn, he⟩ | he
  · obtain ⟨e⟩ := he
    exact card_le_four_of_dihedral hX2 (by omega) e hEX hE
  · obtain ⟨e⟩ := he
    exact card_le_four_of_semidihedral e hEX hE

theorem eight_le_card_of_shape {X : Subgroup G} (hshape : IsDihedralOrSemidihedralShape X) :
    8 ≤ Nat.card X := by
  rcases hshape with ⟨n, hn, he⟩ | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  · obtain ⟨e⟩ := he
    obtain ⟨x, hx⟩ := CFSG.ABGDGroups.semidihedral_exists_orderOf_eq_eight (le_refl 4)
    have h1 := orderOf_dvd_natCard (e.symm x)
    rw [MulEquiv.orderOf_eq, hx] at h1
    exact Nat.le_of_dvd Nat.card_pos h1

end Transport

end CFSG.QuasithinUnique
