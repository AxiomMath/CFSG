module

public import CFSG.CharacterTheory.Semidihedral.ElementStructure

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem map_rotationSubgroup {S : Type*} [Group S] (n : ℕ)
    (f : SemidihedralGroup n ≃* S) :
    (rotationSubgroup n).map (↑f) = Subgroup.zpowers (f (r n)) :=
  f.toMonoidHom.map_zpowers _

theorem map_dihedralSubgroup {S : Type*} [Group S] (n : ℕ)
    (f : SemidihedralGroup n ≃* S) :
    (dihedralSubgroup n).map (↑f) = Subgroup.closure {f (r n) ^ 2, f (s n)} := by
  rw [dihedralSubgroup, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow]
  rfl

theorem map_quaternionSubgroup {S : Type*} [Group S] (n : ℕ)
    (f : SemidihedralGroup n ≃* S) :
    (quaternionSubgroup n).map (↑f) =
      Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)} := by
  rw [quaternionSubgroup, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul]
  rfl

theorem map_commutator_equiv {G S : Type*} [Group G] [Group S] (f : G ≃* S) :
    (commutator G).map (↑f) = commutator S := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective, commutator_def]

theorem mem_map_equiv_iff {G S : Type*} [Group G] [Group S]
    (f : G ≃* S) (H : Subgroup G) (g : G) :
    f g ∈ H.map (↑f) ↔ g ∈ H := by
  constructor
  · rintro ⟨x, hx, h⟩
    have he : x = g := f.injective h
    exact he ▸ hx
  · intro h
    exact ⟨g, h, rfl⟩

theorem map_comap_equiv {G S : Type*} [Group G] [Group S]
    (f : G ≃* S) (H : Subgroup S) :
    (H.comap (f : G →* S)).map (f : G →* S) = H :=
  Subgroup.map_comap_eq_self_of_surjective f.surjective H

theorem index_comap_equiv {G S : Type*} [Group G] [Group S]
    (f : G ≃* S) (H : Subgroup S) : (H.comap (f : G →* S)).index = H.index := by
  rw [← Subgroup.index_map_equiv (H.comap (f : G →* S)) f, map_comap_equiv]

theorem map_subgroup_natCard {G S : Type*} [Group G] [Group S]
    (f : G ≃* S) (H : Subgroup G) : Nat.card (H.map (f : G →* S)) = Nat.card H :=
  (Nat.card_congr (f.subgroupMap H).toEquiv).symm

theorem equiv_orderOf {G S : Type*} [Group G] [Group S]
    (f : G ≃* S) (g : G) : orderOf (f g) = orderOf g :=
  orderOf_injective f.toMonoidHom f.injective g

theorem supplied_center {S : Type*} [Group S] (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) :
    Subgroup.center S = Subgroup.zpowers (f (r n) ^ (modulus n / 2)) ∧
      Nat.card (Subgroup.center S) = 2 := by
  have hz : f (z n) = f (r n) ^ (modulus n / 2) := by
    rw [modulus_div_two n (by omega), z, map_pow]
  constructor
  · rw [← Subgroup.map_center_eq f, center_eq_zpowers n hn, MonoidHom.map_zpowers]
    change Subgroup.zpowers (f (z n)) = _
    rw [hz]
  · rw [← Subgroup.map_center_eq f, map_subgroup_natCard, center_card n hn]

theorem supplied_commutator {S : Type*} [Group S] (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) :
    commutator S = Subgroup.zpowers (f (r n) ^ 2) := by
  rw [← map_commutator_equiv f, commutator_eq_zpowers_r_sq n hn,
    MonoidHom.map_zpowers, map_pow]
  rfl

theorem supplied_index_two {S : Type*} [Group S] (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) (H : Subgroup S) :
    H.index = 2 ↔ H = Subgroup.zpowers (f (r n)) ∨
      H = Subgroup.closure {f (r n) ^ 2, f (s n)} ∨
      H = Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)} := by
  constructor
  · intro h
    have hc := (index_eq_two_iff n (by omega) (H.comap (↑f))).mp
      (by rw [index_comap_equiv]; exact h)
    rcases hc with hA | hD | hQ
    · left
      rw [← map_comap_equiv f H, hA, map_rotationSubgroup]
    · right
      left
      rw [← map_comap_equiv f H, hD, map_dihedralSubgroup]
    · right
      right
      rw [← map_comap_equiv f H, hQ, map_quaternionSubgroup]
  · rintro (rfl | rfl | rfl)
    · rw [← map_rotationSubgroup n f, Subgroup.index_map_equiv]
      exact rotationSubgroup_index n (by omega)
    · rw [← map_dihedralSubgroup n f, Subgroup.index_map_equiv]
      exact dihedralSubgroup_index n (by omega)
    · rw [← map_quaternionSubgroup n f, Subgroup.index_map_equiv]
      exact quaternionSubgroup_index n (by omega)

@[expose] noncomputable def suppliedRotationEquiv {S : Type*} [Group S]
    (n : ℕ) (f : SemidihedralGroup n ≃* S) :
    rotationSubgroup n ≃* Subgroup.zpowers (f (r n)) :=
  (f.subgroupMap (rotationSubgroup n)).trans
    (MulEquiv.subgroupCongr (map_rotationSubgroup n f))

@[expose] noncomputable def suppliedDihedralEquiv {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    DihedralGroup (half n) ≃* Subgroup.closure {f (r n) ^ 2, f (s n)} :=
  (dihedralEquiv n hn).trans ((f.subgroupMap (dihedralSubgroup n)).trans
    (MulEquiv.subgroupCongr (map_dihedralSubgroup n f)))

@[expose] noncomputable def suppliedQuaternionEquiv {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    QuaternionGroup (2 ^ (n - 3)) ≃*
      Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)} :=
  (quaternionEquiv n hn).trans ((f.subgroupMap (quaternionSubgroup n)).trans
    (MulEquiv.subgroupCongr (map_quaternionSubgroup n f)))

theorem suppliedDihedralEquiv_coe {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (g : DihedralGroup (half n)) :
    (suppliedDihedralEquiv n hn f g : S) = f (dihedralHom n hn g) := by
  rfl

theorem suppliedQuaternionEquiv_coe {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S)
    (g : QuaternionGroup (2 ^ (n - 3))) :
    (suppliedQuaternionEquiv n hn f g : S) = f (quaternionHom n hn g) := by
  rfl

theorem suppliedQuaternionEquiv_rotation {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    (suppliedQuaternionEquiv n hn f (QuaternionGroup.a 1) : S) = f (r n) ^ 2 := by
  rw [suppliedQuaternionEquiv_coe, quaternionHom_rotation, map_pow]

theorem suppliedQuaternionEquiv_generator {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    (suppliedQuaternionEquiv n hn f (QuaternionGroup.xa 0) : S) = f (r n) * f (s n) := by
  rw [suppliedQuaternionEquiv_coe, quaternionHom_generator, map_mul]

theorem supplied_subgroup_properties {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    let A := Subgroup.zpowers (f (r n))
    let D := Subgroup.closure {f (r n) ^ 2, f (s n)}
    let Q := Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)}
    A.Normal ∧ D.Normal ∧ Q.Normal ∧ IsCyclic A ∧
      Nat.card A = modulus n ∧ Nat.card D = modulus n ∧ Nat.card Q = modulus n := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_rotationSubgroup n f]
    exact (rotationSubgroup_normal n (by omega)).map (f : SemidihedralGroup n →* S) f.surjective
  · rw [← map_dihedralSubgroup n f]
    exact (dihedralSubgroup_normal n (by omega)).map (f : SemidihedralGroup n →* S) f.surjective
  · rw [← map_quaternionSubgroup n f]
    exact (quaternionSubgroup_normal n (by omega)).map (f : SemidihedralGroup n →* S) f.surjective
  · exact (suppliedRotationEquiv n f).isCyclic.mp (rotationSubgroup_cyclic n)
  · rw [← map_rotationSubgroup n f, map_subgroup_natCard, rotationSubgroup_natCard n (by omega)]
  · rw [← map_dihedralSubgroup n f, map_subgroup_natCard, dihedralSubgroup_natCard n (by omega)]
  · rw [← map_quaternionSubgroup n f, map_subgroup_natCard, quaternionSubgroup_natCard n (by omega)]

theorem supplied_square_formula {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (i : ℤ) :
    (f (r n) ^ i * f (s n)) ^ 2 = (f (r n) ^ (modulus n / 2)) ^ i := by
  have h := congrArg f (reflection_zpow_square n (by omega) i)
  rw [map_pow, map_mul, map_zpow, map_zpow, z, map_pow,
    ← modulus_div_two n (by omega)] at h
  exact h

theorem supplied_involutions {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (g : S) :
    orderOf g = 2 ↔ g = f (r n) ^ (modulus n / 2) ∨
      ∃ j : Fin (modulus n / 2), g = f (r n) ^ (2 * j.val) * f (s n) := by
  obtain ⟨a, rfl⟩ := f.surjective g
  have hz : f (z n) = f (r n) ^ (modulus n / 2) := by
    rw [modulus_div_two n (by omega), z, map_pow]
  rw [equiv_orderOf f a]
  rw [involution_iff n (by omega), modulus_div_two n (by omega)]
  rw [modulus_div_two n (by omega)] at hz
  constructor
  · rintro (h | ⟨j, h⟩)
    · left
      rw [h, hz]
    · right
      refine ⟨j, ?_⟩
      rw [h, map_mul, map_pow]
  · rintro (h | ⟨j, h⟩)
    · left
      apply f.injective
      rw [h, hz]
    · right
      refine ⟨j, f.injective ?_⟩
      rw [map_mul, map_pow]
      exact h

theorem supplied_odd_order_four {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (j : ℤ) :
    orderOf (f (r n) ^ (2 * j + 1) * f (s n)) = 4 := by
  have h := odd_reflection_order n (by omega) j
  rw [← equiv_orderOf f (r n ^ (2 * j + 1) * s n), map_mul, map_zpow] at h
  exact h

theorem supplied_involution_in_dihedral {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S)
    (g : S) (hg : orderOf g = 2) :
    g ∈ Subgroup.closure {f (r n) ^ 2, f (s n)} := by
  obtain ⟨a, rfl⟩ := f.surjective g
  rw [equiv_orderOf f a] at hg
  rw [← map_dihedralSubgroup n f, mem_map_equiv_iff]
  exact involution_mem_dihedralSubgroup n (by omega) a hg

theorem supplied_quaternion_unique_involution {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S)
    (g : S) (hQ : g ∈ Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)})
    (hg : orderOf g = 2) : g = f (r n) ^ (modulus n / 2) := by
  obtain ⟨a, rfl⟩ := f.surjective g
  rw [← map_quaternionSubgroup n f, mem_map_equiv_iff] at hQ
  rw [equiv_orderOf f a] at hg
  rw [quaternion_unique_involution n (by omega) a hQ hg,
    z, map_pow, ← modulus_div_two n (by omega)]

theorem supplied_dihedral_order_four {S : Type*} [Group S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S)
    (g : S) (hg : g ∈ Subgroup.closure {f (r n) ^ 2, f (s n)}) :
    orderOf g = 4 ↔ g = f (r n) ^ (modulus n / 4) ∨
      g = f (r n) ^ (-((modulus n / 4 : ℕ) : ℤ)) := by
  obtain ⟨a, rfl⟩ := f.surjective g
  rw [← map_dihedralSubgroup n f, mem_map_equiv_iff] at hg
  rw [equiv_orderOf f a, dihedral_order_four_iff n hn a hg,
    modulus_div_four n hn, ← map_pow, ← map_zpow,
    f.injective.eq_iff, f.injective.eq_iff]

theorem supplied_index_two_and_element_structure {S : Type*} [Group S] [Finite S]
    (n : ℕ) (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    let r := f (CFSG.Semidihedral.r n)
    let s := f (CFSG.Semidihedral.s n)
    let m := 2 ^ (n - 1)
    let z := r ^ (m / 2)
    let A := Subgroup.zpowers r
    let D := Subgroup.closure {r ^ 2, s}
    let Q := Subgroup.closure {r ^ 2, r * s}
    Subgroup.center S = Subgroup.zpowers z ∧ Nat.card (Subgroup.center S) = 2 ∧
    commutator S = Subgroup.zpowers (r ^ 2) ∧
    (∀ H : Subgroup S, H.index = 2 ↔ H = A ∨ H = D ∨ H = Q) ∧
    A.Normal ∧ D.Normal ∧ Q.Normal ∧ IsCyclic A ∧ Nat.card A = m ∧
    Nonempty (D ≃* DihedralGroup (m / 2)) ∧ Nat.card D = m ∧ Nat.card Q = m ∧
    z ∈ Q ∧ orderOf z = 2 ∧ (∀ g : S, g ∈ Q → orderOf g = 2 → g = z) ∧
    (∀ i : ℤ, (r ^ i * s) ^ 2 = z ^ i) ∧
    (∀ g : S, orderOf g = 2 ↔ g = z ∨
      ∃ j : Fin (m / 2), g = r ^ (2 * j.val) * s) ∧
    (∀ j : ℤ, orderOf (r ^ (2 * j + 1) * s) = 4) ∧
    (∀ g : S, orderOf g = 2 → g ∈ D) ∧
    (∀ g : S, g ∈ D → (orderOf g = 4 ↔
      g = r ^ (m / 4) ∨ g = r ^ (-((m / 4 : ℕ) : ℤ)))) := by
  dsimp only
  change Subgroup.center S = Subgroup.zpowers (f (r n) ^ (modulus n / 2)) ∧ _
  have hprops := supplied_subgroup_properties n hn f
  have hz : f (z n) = f (r n) ^ (modulus n / 2) := by
    rw [modulus_div_two n (by omega), z, map_pow]
  have hzmem : f (r n) ^ (modulus n / 2) ∈
      Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)} := by
    rw [← hz, ← map_quaternionSubgroup n f, mem_map_equiv_iff]
    exact z_mem_quaternionSubgroup n (by omega)
  have hzorder : orderOf (f (r n) ^ (modulus n / 2)) = 2 := by
    rw [← hz, equiv_orderOf]
    exact orderOf_z n (by omega)
  have hd : Nonempty (Subgroup.closure {f (r n) ^ 2, f (s n)} ≃*
      DihedralGroup (modulus n / 2)) := by
    rw [modulus_div_two n (by omega)]
    exact ⟨(suppliedDihedralEquiv n hn f).symm⟩
  exact ⟨(supplied_center n hn f).1, (supplied_center n hn f).2,
    supplied_commutator n hn f, supplied_index_two n hn f,
    hprops.1, hprops.2.1, hprops.2.2.1, hprops.2.2.2.1, hprops.2.2.2.2.1,
    hd, hprops.2.2.2.2.2.1, hprops.2.2.2.2.2.2,
    hzmem, hzorder, supplied_quaternion_unique_involution n hn f,
    supplied_square_formula n hn f, supplied_involutions n hn f,
    supplied_odd_order_four n hn f, supplied_involution_in_dihedral n hn f,
    supplied_dihedral_order_four n hn f⟩

end CFSG.Semidihedral
