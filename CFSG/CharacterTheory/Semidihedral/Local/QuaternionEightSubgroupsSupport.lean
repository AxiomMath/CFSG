module

public import CFSG.CharacterTheory.Semidihedral.Local.ProperSubgroupForms

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open QuaternionGroup

variable {S : Type*} [Group S] {n : ℕ}

section Arithmetic

theorem modulus_eq_eight_mul (hn : 4 ≤ n) : modulus n = 8 * 2 ^ (n - 4) := by
  rw [modulus, show n - 1 = (n - 4) + 3 by omega, pow_add]
  ring

theorem four_mul_quarter (hn : 4 ≤ n) :
    (4 : ZMod (modulus n)) * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) = 0 :=
  (four_mul_eq_zero_iff hn _).mpr ⟨1, by rw [Nat.cast_one, one_mul]⟩

theorem half_eq_two_mul_quarter_residue (hn3 : 3 ≤ n) :
    (half n : ZMod (modulus n)) = 2 * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
  rw [half_eq_two_mul_quarter hn3, Nat.cast_mul, Nat.cast_ofNat]

theorem half_eq_four_mul_eighth_residue (hn : 4 ≤ n) :
    (half n : ZMod (modulus n)) = 4 * ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) := by
  have h : half n = 4 * 2 ^ (n - 4) := by
    rw [half, show n - 2 = (n - 4) + 2 by omega, pow_add]
    ring
  rw [h, Nat.cast_mul, Nat.cast_ofNat]

theorem eight_mul_eq_zero_iff (hn : 4 ≤ n) (k : ZMod (modulus n)) :
    8 * k = 0 ↔
      ∃ c : ℕ, k = (c : ZMod (modulus n)) * ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) := by
  have hm := modulus_eq_eight_mul hn
  constructor
  · intro hk
    have hcast : ((8 * k.val : ℕ) : ZMod (modulus n)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact_mod_cast hk
    rw [ZMod.natCast_eq_zero_iff] at hcast
    have hcast' : 8 * 2 ^ (n - 4) ∣ 8 * k.val := by rw [← hm]; exact hcast
    obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hcast'
    refine ⟨c, ?_⟩
    rw [← ZMod.natCast_zmod_val k, hc, Nat.cast_mul, mul_comm]
  · rintro ⟨c, rfl⟩
    have h8 : (8 : ZMod (modulus n)) * ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) = 0 := by
      rw [show (8 : ZMod (modulus n)) = ((8 : ℕ) : ZMod (modulus n)) by norm_cast,
        ← Nat.cast_mul, ← hm, ZMod.natCast_self]
    linear_combination (c : ZMod (modulus n)) * h8

theorem eight_mul_eighth (hn : 4 ≤ n) :
    (8 : ZMod (modulus n)) * ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) = 0 :=
  (eight_mul_eq_zero_iff hn _).mpr ⟨1, by rw [Nat.cast_one, one_mul]⟩

theorem four_mul_one_sub_twist_mul_eq_zero_iff (hn : 4 ≤ n) (k : ZMod (modulus n)) :
    4 * ((1 - twist n) * k) = 0 ↔ 8 * k = 0 := by
  have ht := twist_sub_one_eq_two_mul n hn
  have h : 4 * ((1 - twist n) * k) =
      -(((2 ^ (n - 3) - 1 : ℕ) : ZMod (modulus n)) * (8 * k)) := by
    linear_combination (-4 * k) * ht
  rw [h, neg_eq_zero, (quarter_sub_one_isUnit n hn).mul_right_eq_zero]

theorem twist_mul_eighth (hn : 5 ≤ n) :
    twist n * ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) =
      -((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) := by
  have hprod : ((half n * 2 ^ (n - 4) : ℕ) : ZMod (modulus n)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    refine ⟨2 ^ (n - 5), ?_⟩
    rw [half, modulus, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [twist, Nat.cast_mul] at *
  linear_combination hprod

theorem intCast_val_mod_two (hn3 : 3 ≤ n) {i : ℤ} (hi : Odd i) :
    ((i : ZMod (modulus n))).val % 2 = 1 := by
  have h := ZMod.val_intCast (n := modulus n) i
  have hdvd : (2 : ℤ) ∣ (modulus n : ℤ) := by
    rw [modulus]
    push_cast
    exact dvd_pow_self 2 (by omega)
  have h2 : ((i : ZMod (modulus n)).val : ℤ) % 2 = i % 2 := by
    rw [h, Int.emod_emod_of_dvd i hdvd]
  obtain ⟨t, rfl⟩ := hi
  omega

theorem eq_two_mul_add_one_of_val_mod_two {k : ZMod (modulus n)} (hk : k.val % 2 = 1) :
    k = 2 * ((k.val / 2 : ℕ) : ZMod (modulus n)) + 1 := by
  have h := Nat.div_add_mod k.val 2
  rw [hk] at h
  calc k = ((k.val : ℕ) : ZMod (modulus n)) := (ZMod.natCast_zmod_val k).symm
    _ = ((2 * (k.val / 2) + 1 : ℕ) : ZMod (modulus n)) := by rw [h]
    _ = 2 * ((k.val / 2 : ℕ) : ZMod (modulus n)) + 1 := by push_cast; ring

end Arithmetic

section Coordinates

theorem image_zpow_mul_s_eq (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S) (i : ℤ) :
    f (r n) ^ i * f (s n) = f (element n hn3 (i : ZMod (modulus n)) 1) := by
  rw [← map_zpow, ← map_mul, r_zpow_eq_element n hn3, s_eq_element n hn3, element_rotation_mul,
    add_zero]

theorem image_eighth_eq (hn : 4 ≤ n) (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S) :
    f (r n) ^ (2 ^ (n - 1) / 8) =
      f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0) := by
  have h : 2 ^ (n - 1) / 8 = 2 ^ (n - 4) := by
    rw [show n - 1 = (n - 4) + 3 by omega, pow_add, show (2 : ℕ) ^ 3 = 8 by norm_num,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [h, image_r_pow_eq hn3]

theorem image_rotation_pow (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (j : ZMod (modulus n)) (k : ℕ) :
    f (element n hn3 j 0) ^ k = f (element n hn3 ((k : ZMod (modulus n)) * j) 0) := by
  rw [← map_pow, element_rotation_pow, nsmul_eq_mul]

theorem image_reflection_eq_mul (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i j : ZMod (modulus n)) :
    f (element n hn3 j 1) = f (element n hn3 (j - i) 0) * f (element n hn3 i 1) := by
  rw [image_rotation_mul, sub_add_cancel]

theorem image_rotation_mem (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S) (j : ZMod (modulus n)) :
    f (element n hn3 j 0) ∈ Subgroup.zpowers (f (r n)) :=
  (image_element_mem_zpowers_r_iff hn3 f j 0).mpr rfl

theorem image_reflection_notMem (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (j : ZMod (modulus n)) : f (element n hn3 j 1) ∉ Subgroup.zpowers (f (r n)) := by
  rw [image_element_mem_zpowers_r_iff]
  decide

theorem image_odd_reflection_sq (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    {i : ZMod (modulus n)} (hi : i.val % 2 = 1) :
    f (element n hn3 i 1) ^ 2 = f (element n hn3 (half n : ZMod (modulus n)) 0) := by
  rw [← map_pow, element_reflection_sq, (half_mul_eq_half_iff n hn3 i).mpr hi]

theorem center_map_subtype_eq (Q : Subgroup S) :
    (Subgroup.center Q).map Q.subtype = Q ⊓ Subgroup.centralizer (Q : Set S) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hq ⟨h, hh⟩)
  · rintro ⟨hyQ, hyC⟩
    refine ⟨⟨y, hyQ⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hyC g g.2

end Coordinates

section QuaternionEight

variable (hn : 4 ≤ n) (hn3 : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
  {i : ZMod (modulus n)} (hi : i.val % 2 = 1) {v x : S}
  (hv : v = f (element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0))
  (hx : x = f (element n hn3 i 1)) {Q : Subgroup S} (hQ : Q = Subgroup.closure {v, x})

include hn hv hx hi in
theorem quaternionEight_relations :
    orderOf v = 2 * 2 ∧ x ∉ Subgroup.zpowers v ∧ x ^ 2 = v ^ 2 ∧ x * v * x⁻¹ = v⁻¹ := by
  refine ⟨?_, fun h => ?_, ?_, ?_⟩
  · rw [hv, equiv_orderOf, rotation_order_four_iff n hn]
    exact Or.inl rfl
  · have hle : Subgroup.zpowers v ≤ Subgroup.zpowers (f (r n)) :=
      Subgroup.zpowers_le.mpr (hv ▸ image_rotation_mem hn3 f _)
    exact image_reflection_notMem hn3 f i (hx ▸ hle h)
  · rw [hx, hv, image_odd_reflection_sq hn3 f hi, image_rotation_pow,
      half_eq_two_mul_quarter_residue hn3, Nat.cast_ofNat]
  · have h : element n hn3 i 1 * element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0 *
        (element n hn3 i 1)⁻¹ = (element n hn3 ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0)⁻¹ := by
      rw [conjugate_rotation_by_reflection, twist_mul_quarter hn, element_rotation_inv]
    rw [hx, hv]
    simpa only [map_mul, map_inv] using congrArg f h

include hn hv hx hi hQ in
theorem quaternionEight_equiv :
    ∃ e : QuaternionGroup 2 ≃* Q,
      ∀ j : ZMod (2 * 2), (e (a j) : S) = v ^ j.val ∧ (e (xa j) : S) = x * v ^ j.val := by
  obtain ⟨hvo, hxv, hx2, hxvx⟩ := quaternionEight_relations hn hn3 f hi hv hx
  have hvQ : v ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hxQ : x ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hgen := closure_pair_subtype_eq_top hvQ hxQ hQ
  have hvo' : orderOf (⟨v, hvQ⟩ : Q) = 2 * 2 := by rw [Subgroup.orderOf_mk, hvo]
  have hxv' : (⟨x, hxQ⟩ : Q) ∉ Subgroup.zpowers (⟨v, hvQ⟩ : Q) := fun h => by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    exact hxv (Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩)
  have hx2' : (⟨x, hxQ⟩ : Q) ^ 2 = (⟨v, hvQ⟩ : Q) ^ 2 := Subtype.ext (by simpa using hx2)
  have hxvx' : (⟨x, hxQ⟩ : Q) * ⟨v, hvQ⟩ * (⟨x, hxQ⟩ : Q)⁻¹ = (⟨v, hvQ⟩ : Q)⁻¹ :=
    Subtype.ext (by simpa using hxvx)
  obtain ⟨⟨e, ⟨he1, he2⟩, -⟩, hform⟩ :=
    quaternion_normal_form_isomorphism (m := 2) (by norm_num) hgen hvo' hxv' hx2' hxvx'
  refine ⟨e, fun j => ⟨?_, ?_⟩⟩
  · rw [((hform e he1 he2) j).1, Subgroup.coe_pow]
  · rw [((hform e he1 he2) j).2, Subgroup.coe_mul, Subgroup.coe_pow]

include hn hv hx hi hQ in
theorem mem_quaternionEight_iff (j : ZMod (modulus n)) (e : ZMod 2) :
    f (element n hn3 j e) ∈ Q ↔ (e = 0 ∧ 4 * j = 0) ∨ (e = 1 ∧ 4 * (j - i) = 0) := by
  obtain ⟨φ, hφ⟩ := quaternionEight_equiv hn hn3 f hi hv hx hQ
  have hq4 := four_mul_quarter hn
  have hvQ : v ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hxQ : x ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hvpow : ∀ k : ℕ, v ^ k = f (element n hn3
      ((k : ZMod (modulus n)) * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n))) 0) := fun k => by
    rw [hv, image_rotation_pow]
  constructor
  · intro hmem
    obtain ⟨t, ht⟩ := φ.surjective ⟨_, hmem⟩
    have ht' : (φ t : S) = f (element n hn3 j e) := congrArg Subtype.val ht
    rcases t with k | k
    · rw [(hφ k).1, hvpow, image_element_eq_iff] at ht'
      obtain ⟨hj, he⟩ := ht'
      refine Or.inl ⟨he.symm, ?_⟩
      rw [← hj]
      linear_combination (k.val : ZMod (modulus n)) * hq4
    · rw [(hφ k).2, hvpow, hx, image_reflection_mul, image_element_eq_iff] at ht'
      obtain ⟨hj, he⟩ := ht'
      refine Or.inr ⟨by rw [← he, add_zero], ?_⟩
      rw [← hj]
      linear_combination (twist n * (k.val : ZMod (modulus n))) * hq4
  · rintro (⟨rfl, hj⟩ | ⟨rfl, hj⟩)
    · obtain ⟨c, rfl⟩ := (four_mul_eq_zero_iff hn j).mp hj
      rw [← hvpow]
      exact Subgroup.pow_mem _ hvQ c
    · obtain ⟨c, hc⟩ := (four_mul_eq_zero_iff hn (j - i)).mp hj
      rw [image_reflection_eq_mul hn3 f i j, hc, ← hvpow, ← hx]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hvQ c) hxQ

include hn hv hx hQ in
theorem centralizer_quaternionEight :
    Subgroup.centralizer (Q : Set S) = Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2)) := by
  have hvQ : v ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hxQ : x ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    obtain ⟨j, e, rfl⟩ := exists_coordinates hn3 f g
    have hgx := hg x hxQ
    have hgv := hg v hvQ
    rw [hx] at hgx
    rcases (image_commute_reflection_iff hn f i j e).mp hgx.symm with
      ⟨rfl, rfl | rfl⟩ | ⟨rfl, -⟩
    · rw [element_zero_zero, map_one]
      exact Subgroup.one_mem _
    · rw [image_z_eq hn3 f]
      exact Subgroup.mem_zpowers _
    · exfalso
      rw [hv, image_rotation_mul, image_reflection_mul, image_element_eq_iff,
        twist_mul_quarter hn] at hgv
      have h2 : 2 * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) = 0 := by linear_combination hgv.1
      rw [← half_eq_two_mul_quarter_residue hn3] at h2
      exact half_residue_ne_zero n hn3 h2
  · rw [Subgroup.zpowers_le]
    exact Subgroup.center_le_centralizer _ (image_z_mem_center hn f)

include hn hv hx hQ in
theorem center_quaternionEight :
    (Subgroup.center Q).map Q.subtype = Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2)) := by
  have hvQ : v ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  rw [center_map_subtype_eq, centralizer_quaternionEight hn hn3 f hv hx hQ]
  apply inf_eq_right.mpr
  rw [Subgroup.zpowers_le, image_z_eq hn3 f, half_eq_two_mul_quarter_residue hn3,
    ← Nat.cast_ofNat (R := ZMod (modulus n)) (n := 2), ← image_rotation_pow, ← hv]
  exact Subgroup.pow_mem _ hvQ 2

include hn hv hx hi hQ in
theorem normalizer_quaternionEight :
    Subgroup.normalizer (Q : Set S) =
      Subgroup.closure {f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0), x} := by
  have := finite_of_semidihedral hn3 f
  have hvQ : v ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hxQ : x ∈ Q := hQ ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmem := mem_quaternionEight_iff hn hn3 f hi hv hx hQ
  have hcrit : ∀ g : S, g ∈ Subgroup.normalizer (Q : Set S) ↔
      g * v * g⁻¹ ∈ Q ∧ g * x * g⁻¹ ∈ Q := by
    intro g
    constructor
    · intro hg
      exact ⟨(Subgroup.mem_normalizer_iff.mp hg v).mp hvQ,
        (Subgroup.mem_normalizer_iff.mp hg x).mp hxQ⟩
    · rintro ⟨h1, h2⟩
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      have hle : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
        rw [hQ, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨w, hw, rfl⟩
        rcases hw with rfl | rfl
        · exact hQ ▸ h1
        · exact hQ ▸ h2
      exact hle ⟨y, hy, rfl⟩
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hrot : ∀ k : ZMod (modulus n),
      f (element n hn3 k 0) ∈ Subgroup.normalizer (Q : Set S) ↔ 8 * k = 0 := by
    intro k
    have h1 : f (element n hn3 k 0) * v * (f (element n hn3 k 0))⁻¹ = v := by
      rw [hv, ← map_inv, ← map_mul, ← map_mul, conjugate_rotation_by_rotation]
    have h2 : f (element n hn3 k 0) * x * (f (element n hn3 k 0))⁻¹ =
        f (element n hn3 (i + (1 - twist n) * k) 1) := by
      rw [hx, ← map_inv, ← map_mul, ← map_mul, conjugate_reflection_by_rotation]
    rw [hcrit, h1, h2, hmem, add_sub_cancel_left, four_mul_one_sub_twist_mul_eq_zero_iff hn]
    constructor
    · rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩
      · exact absurd h h10
      · exact h
    · intro h
      exact ⟨hvQ, Or.inr ⟨rfl, h⟩⟩
  have hxN : x ∈ Subgroup.normalizer (Q : Set S) := Subgroup.le_normalizer hxQ
  have hwmem : f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0) ∈
      Subgroup.closure {f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0), x} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hxmem : x ∈
      Subgroup.closure {f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0), x} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrotmem : ∀ k : ZMod (modulus n), 8 * k = 0 → f (element n hn3 k 0) ∈
      Subgroup.closure {f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0), x} := by
    intro k hk
    obtain ⟨c, rfl⟩ := (eight_mul_eq_zero_iff hn k).mp hk
    rw [← image_rotation_pow]
    exact Subgroup.pow_mem _ hwmem c
  apply le_antisymm
  · intro g hg
    obtain ⟨k, e, rfl⟩ := exists_coordinates hn3 f g
    rcases exponent_cases e with rfl | rfl
    · exact hrotmem k ((hrot k).mp hg)
    · rw [image_reflection_eq_mul hn3 f i k, ← hx] at hg ⊢
      have hk : f (element n hn3 (k - i) 0) ∈ Subgroup.normalizer (Q : Set S) := by
        have h := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hxN)
        rwa [mul_inv_cancel_right] at h
      exact Subgroup.mul_mem _ (hrotmem _ ((hrot _).mp hk)) hxmem
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact (hrot _).mpr (eight_mul_eighth hn)
    · exact hxN

include hx in
theorem closure_eighth_eq_top (h4 : n = 4) :
    Subgroup.closure {f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0), x} = ⊤ := by
  have h1 : ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) = 1 := by
    rw [h4]
    norm_num
  rw [h1, eq_top_iff]
  intro g _
  have hwmem : f (element n hn3 1 0) ∈ Subgroup.closure {f (element n hn3 1 0), x} :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hxmem : x ∈ Subgroup.closure {f (element n hn3 1 0), x} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrotmem : ∀ k : ZMod (modulus n),
      f (element n hn3 k 0) ∈ Subgroup.closure {f (element n hn3 1 0), x} := by
    intro k
    have h := Subgroup.pow_mem _ hwmem k.val
    rwa [image_rotation_pow, mul_one, ZMod.natCast_zmod_val] at h
  obtain ⟨k, e, rfl⟩ := exists_coordinates hn3 f g
  rcases exponent_cases e with rfl | rfl
  · exact hrotmem k
  · rw [image_reflection_eq_mul hn3 f i k, ← hx]
    exact Subgroup.mul_mem _ (hrotmem _) hxmem

include hi hx in
theorem eighth_relations (hn5 : 5 ≤ n) {u : S}
    (hu : u = f (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0)) :
    orderOf u = 2 * 4 ∧ x ∉ Subgroup.zpowers u ∧ x ^ 2 = u ^ 4 ∧ x * u * x⁻¹ = u⁻¹ := by
  have hn4 : 4 ≤ n := by omega
  refine ⟨?_, fun h => ?_, ?_, ?_⟩
  · rw [hu, ← image_r_pow_eq hn3, orderOf_pow_of_dvd (by positivity)
      (by rw [sd_orderOf_r hn4]; exact Nat.pow_dvd_pow 2 (by omega)), sd_orderOf_r hn4,
      Nat.pow_div (by omega) (by norm_num), show n - 1 - (n - 4) = 3 by omega]
  · have hle : Subgroup.zpowers u ≤ Subgroup.zpowers (f (r n)) :=
      Subgroup.zpowers_le.mpr (hu ▸ image_rotation_mem hn3 f _)
    exact image_reflection_notMem hn3 f i (hx ▸ hle h)
  · rw [hx, hu, image_odd_reflection_sq hn3 f hi, image_rotation_pow,
      half_eq_four_mul_eighth_residue hn4, Nat.cast_ofNat]
  · have h : element n hn3 i 1 * element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0 *
        (element n hn3 i 1)⁻¹ = (element n hn3 ((2 ^ (n - 4) : ℕ) : ZMod (modulus n)) 0)⁻¹ := by
      rw [conjugate_rotation_by_reflection, twist_mul_eighth hn5, element_rotation_inv]
    rw [hx, hu]
    simpa only [map_mul, map_inv] using congrArg f h

include hn hv in
theorem quaternionEight_conj {j : ZMod (modulus n)} (hi : i.val % 2 = 1) (hj : j.val % 2 = 1) :
    ∃ g ∈ Subgroup.zpowers (f (r n)),
      Subgroup.closure {v, f (element n hn3 j 1)} =
        (Subgroup.closure {v, f (element n hn3 i 1)}).map (MulAut.conj g).toMonoidHom := by
  set c : ZMod (modulus n) := ((j.val / 2 : ℕ) : ZMod (modulus n)) -
    ((i.val / 2 : ℕ) : ZMod (modulus n)) with hc
  have hji : j - i = 2 * c := by
    rw [hc]
    linear_combination eq_two_mul_add_one_of_val_mod_two hj -
      eq_two_mul_add_one_of_val_mod_two hi
  obtain ⟨u, hu⟩ := quarter_sub_one_isUnit n hn
  have hmul : (1 - twist n) * (-(↑u⁻¹ * c)) = j - i := by
    have huinv : (u : ZMod (modulus n)) * ↑u⁻¹ = 1 := Units.mul_inv u
    rw [hji]
    linear_combination (↑u⁻¹ * c) * twist_sub_one_eq_two_mul n hn - (2 * c * ↑u⁻¹) * hu +
      (2 * c) * huinv
  obtain ⟨g, hg⟩ : ∃ g : S, g = f (element n hn3 (-(↑u⁻¹ * c)) 0) := ⟨_, rfl⟩
  refine ⟨g, hg ▸ image_rotation_mem hn3 f _, ?_⟩
  have hgv : MulAut.conj g v = v := by
    rw [MulAut.conj_apply, hg, hv, ← map_inv, ← map_mul, ← map_mul,
      conjugate_rotation_by_rotation]
  have hgx : MulAut.conj g (f (element n hn3 i 1)) = f (element n hn3 j 1) := by
    rw [MulAut.conj_apply, hg, ← map_inv, ← map_mul, ← map_mul,
      conjugate_reflection_by_rotation, hmul, add_sub_cancel]
  rw [MonoidHom.map_closure, Set.image_pair]
  change Subgroup.closure {v, f (element n hn3 j 1)} =
    Subgroup.closure {MulAut.conj g v, MulAut.conj g (f (element n hn3 i 1))}
  rw [hgv, hgx]

end QuaternionEight

theorem quaternionGroup_two_sq_eq_one :
    ∀ g : QuaternionGroup 2, g ^ 2 = 1 → g = 1 ∨ g = a 2 := by
  decide

theorem quaternionGroup_two_not_comm :
    (a 1 : QuaternionGroup 2) * xa 0 ≠ xa 0 * a 1 := by
  decide

theorem dihedral_ne_quaternionGroup_two {h : ℕ} (hh : h ≠ 1)
    (φ : DihedralGroup h ≃* QuaternionGroup 2) : False := by
  have hne : (DihedralGroup.sr 0 : DihedralGroup h) ≠ DihedralGroup.sr 1 := by
    intro h01
    have : Nontrivial (ZMod h) := ZMod.nontrivial_iff.mpr hh
    exact zero_ne_one (DihedralGroup.sr.inj h01)
  have hsq : ∀ j : ZMod h, φ (DihedralGroup.sr j) = a 2 := by
    intro j
    have h1 : φ (DihedralGroup.sr j) ^ 2 = 1 := by
      rw [← map_pow, pow_two, DihedralGroup.sr_mul_self, map_one]
    rcases quaternionGroup_two_sq_eq_one _ h1 with h | h
    · exfalso
      rw [← map_one φ] at h
      have := φ.injective h
      rw [DihedralGroup.one_def] at this
      cases this
    · exact h
  exact hne (φ.injective ((hsq 0).trans (hsq 1).symm))

end CFSG.Semidihedral.Local
