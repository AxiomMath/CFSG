module

public import CFSG.CharacterTheory.Semidihedral.KleinFourOddKernel
public import CFSG.CharacterTheory.Semidihedral.Conjugacy
public import CFSG.CharacterTheory.Semidihedral.StructureTransport

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

variable {S : Type*} [Group S] {n : ℕ}

section Coordinates

theorem finite_of_semidihedral (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S) : Finite S :=
  @Finite.of_equiv _ _ (presentation_finite n hn) f.toEquiv

theorem exists_coordinates (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S) (g : S) :
    ∃ i e, g = f (element n hn i e) :=
  ⟨(coordinateEquiv n hn (f.symm g)).1, (coordinateEquiv n hn (f.symm g)).2, by
    rw [element_coordinates, MulEquiv.apply_symm_apply]⟩

theorem image_r_pow_eq (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S) (k : ℕ) :
    f (r n) ^ k = f (element n hn (k : ZMod (modulus n)) 0) := by
  rw [← map_pow, r_pow_eq_element n hn]

theorem image_z_eq (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S) :
    f (r n) ^ (2 ^ (n - 1) / 2) = f (element n hn (half n : ZMod (modulus n)) 0) := by
  rw [show 2 ^ (n - 1) / 2 = half n from modulus_div_two n hn, image_r_pow_eq hn]

theorem image_quarter_eq (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    f (r n) ^ (2 ^ (n - 1) / 4) =
      f (element n (Nat.le_of_succ_le hn) ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) 0) := by
  rw [show 2 ^ (n - 1) / 4 = 2 ^ (n - 3) from modulus_div_four n hn,
    image_r_pow_eq (Nat.le_of_succ_le hn)]

theorem image_rotation_mul (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i j : ZMod (modulus n)) (e : ZMod 2) :
    f (element n hn i 0) * f (element n hn j e) = f (element n hn (i + j) e) := by
  rw [← map_mul, element_rotation_mul]

theorem image_reflection_mul (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i j : ZMod (modulus n)) (e : ZMod 2) :
    f (element n hn i 1) * f (element n hn j e) =
      f (element n hn (i + twist n * j) (1 + e)) := by
  rw [← map_mul, element_reflection_mul]

theorem image_element_eq_iff (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i j : ZMod (modulus n)) (e e' : ZMod 2) :
    f (element n hn i e) = f (element n hn j e') ↔ i = j ∧ e = e' := by
  rw [f.injective.eq_iff, element_eq_iff]

theorem image_element_eq_one_iff (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    f (element n hn i e) = 1 ↔ i = 0 ∧ e = 0 := by
  rw [MulEquivClass.map_eq_one_iff, element_eq_one_iff]

theorem image_element_mem_zpowers_r_iff (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    f (element n hn i e) ∈ Subgroup.zpowers (f (r n)) ↔ e = 0 := by
  rw [← map_rotationSubgroup n f, mem_map_equiv_iff, element_mem_rotationSubgroup_iff]

theorem image_rotation_orderOf_eq_two_iff (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i : ZMod (modulus n)) :
    orderOf (f (element n hn i 0)) = 2 ↔ i = (half n : ZMod (modulus n)) := by
  rw [equiv_orderOf, rotation_involution_iff]

theorem image_reflection_orderOf_eq_two_iff (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i : ZMod (modulus n)) :
    orderOf (f (element n hn i 1)) = 2 ↔ i.val % 2 = 0 := by
  rw [equiv_orderOf, outside_involution_iff]

theorem image_z_mem_center (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    f (r n) ^ (2 ^ (n - 1) / 2) ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨i, e, rfl⟩ := exists_coordinates (Nat.le_of_succ_le hn) f g
  have hz := Subgroup.mem_center_iff.mp (z_mem_center n hn) (element n (Nat.le_of_succ_le hn) i e)
  rw [z_eq_element n (Nat.le_of_succ_le hn)] at hz
  rw [image_z_eq (Nat.le_of_succ_le hn), ← map_mul, ← map_mul, hz]

theorem image_z_orderOf (hn : 3 ≤ n) (f : SemidihedralGroup n ≃* S) :
    orderOf (f (r n) ^ (2 ^ (n - 1) / 2)) = 2 := by
  rw [image_z_eq hn, image_rotation_orderOf_eq_two_iff]

theorem exists_reflection_coordinates (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (x : S)
    (hx : orderOf x = 2) (hxz : x ∉ Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2))) :
    ∃ i : ZMod (modulus n), i.val % 2 = 0 ∧ x = f (element n (Nat.le_of_succ_le hn) i 1) := by
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  obtain ⟨i, e, rfl⟩ := exists_coordinates hn3 f x
  rcases exponent_cases e with rfl | rfl
  · rw [image_rotation_orderOf_eq_two_iff] at hx
    subst hx
    exact absurd (by rw [image_z_eq hn3]; exact Subgroup.mem_zpowers _) hxz
  · exact ⟨i, (image_reflection_orderOf_eq_two_iff hn3 f i).mp hx, rfl⟩

end Coordinates

section Arithmetic

theorem one_sub_twist_mul_mem_iff (hn : 4 ≤ n) (k : ZMod (modulus n)) :
    ((1 - twist n) * k = 0 ∨ (1 - twist n) * k = (half n : ZMod (modulus n))) ↔
      4 * k = 0 := by
  rw [← two_mul_eq_zero_iff n (Nat.le_of_succ_le hn)]
  have ht := twist_sub_one_eq_two_mul n hn
  have h : 2 * ((1 - twist n) * k) =
      -(((2 ^ (n - 3) - 1 : ℕ) : ZMod (modulus n)) * (4 * k)) := by
    linear_combination (-2 * k) * ht
  rw [h, neg_eq_zero, (quarter_sub_one_isUnit n hn).mul_right_eq_zero]

theorem four_mul_eq_zero_iff (hn : 4 ≤ n) (k : ZMod (modulus n)) :
    4 * k = 0 ↔ ∃ c : ℕ, k = (c : ZMod (modulus n)) * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
  have hm : modulus n = 4 * 2 ^ (n - 3) := by
    rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_quarter (by omega)]
    ring
  constructor
  · intro hk
    have hcast : ((4 * k.val : ℕ) : ZMod (modulus n)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact_mod_cast hk
    rw [ZMod.natCast_eq_zero_iff] at hcast
    have hcast' : 4 * 2 ^ (n - 3) ∣ 4 * k.val := by rw [← hm]; exact hcast
    obtain ⟨c, hc⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hcast'
    refine ⟨c, ?_⟩
    rw [← ZMod.natCast_zmod_val k, hc, Nat.cast_mul, mul_comm]
  · rintro ⟨c, rfl⟩
    have h4 : (4 : ZMod (modulus n)) * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) = 0 := by
      rw [show (4 : ZMod (modulus n)) = ((4 : ℕ) : ZMod (modulus n)) by norm_cast,
        ← Nat.cast_mul, ← hm, ZMod.natCast_self]
    linear_combination (c : ZMod (modulus n)) * h4

theorem twist_mul_quarter (hn : 4 ≤ n) :
    twist n * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) = -((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
  have hprod : ((half n * 2 ^ (n - 3) : ℕ) : ZMod (modulus n)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    refine ⟨2 ^ (n - 4), ?_⟩
    rw [half, modulus, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [twist, Nat.cast_mul] at *
  linear_combination hprod

end Arithmetic

section Centralizer

theorem image_commute_reflection_iff (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i j : ZMod (modulus n)) (e : ZMod 2) :
    f (element n (Nat.le_of_succ_le hn) j e) * f (element n (Nat.le_of_succ_le hn) i 1) =
        f (element n (Nat.le_of_succ_le hn) i 1) * f (element n (Nat.le_of_succ_le hn) j e) ↔
      (e = 0 ∧ (j = 0 ∨ j = (half n : ZMod (modulus n)))) ∨
        (e = 1 ∧ (j = i ∨ j = (half n : ZMod (modulus n)) + i)) := by
  have hfix := twist_fixed_iff n hn
  rcases exponent_cases e with rfl | rfl
  · rw [image_rotation_mul, image_reflection_mul, image_element_eq_iff]
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    constructor
    · rintro ⟨h, -⟩
      exact Or.inl ⟨rfl, (hfix j).mp (by linear_combination -h)⟩
    · rintro (⟨-, hj⟩ | ⟨h, -⟩)
      · exact ⟨by linear_combination -((hfix j).mpr hj), rfl⟩
      · exact absurd h h01
  · rw [image_reflection_mul, image_reflection_mul, image_element_eq_iff]
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    have hsub : ∀ w : ZMod (modulus n), (w = 0 ∨ w = (half n : ZMod (modulus n))) →
        (w + i = i ∨ w + i = (half n : ZMod (modulus n)) + i) := by
      rintro w (rfl | rfl)
      · exact Or.inl (zero_add i)
      · exact Or.inr rfl
    constructor
    · rintro ⟨h, -⟩
      refine Or.inr ⟨rfl, ?_⟩
      have h' : twist n * (j - i) = j - i := by linear_combination -h
      simpa only [sub_add_cancel] using hsub (j - i) ((hfix (j - i)).mp h')
    · rintro (⟨h, -⟩ | ⟨-, hj⟩)
      · exact absurd h h10
      · refine ⟨?_, rfl⟩
        have hw : j - i = 0 ∨ j - i = (half n : ZMod (modulus n)) := by
          rcases hj with rfl | rfl
          · exact Or.inl (sub_self j)
          · exact Or.inr (add_sub_cancel_right _ _)
        linear_combination -((hfix (j - i)).mpr hw)

theorem closure_pair_eq_sup (a b : S) :
    Subgroup.closure {a, b} = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure]

theorem centralizer_eq_closure (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (x : S)
    (hx : orderOf x = 2) (hxz : x ∉ Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2))) :
    Subgroup.centralizer {x} = Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 2), x} ∧
      IsKleinFour (Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 2), x}) := by
  have := finite_of_semidihedral (Nat.le_of_succ_le hn) f
  set z := f (r n) ^ (2 ^ (n - 1) / 2) with hzdef
  have hzc : z ∈ Subgroup.center S := image_z_mem_center hn f
  have hz2 : orderOf z = 2 := image_z_orderOf (Nat.le_of_succ_le hn) f
  have hzx : z ≠ x := fun h => hxz (h ▸ Subgroup.mem_zpowers z)
  have hcl : Subgroup.closure {z, x} = KleinFourOddKernel.fourSubgroup z x :=
    closure_pair_eq_sup z x
  refine ⟨?_, hcl ▸ KleinFourOddKernel.fourSubgroup_isKleinFour z x hzc hz2 hx hzx⟩
  obtain ⟨i, -, rfl⟩ := exists_reflection_coordinates hn f x hx hxz
  have hz : z = f (element n (Nat.le_of_succ_le hn) (half n : ZMod (modulus n)) 0) := image_z_eq _ f
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, hcl,
    KleinFourOddKernel.mem_fourSubgroup z _ g hzc hz2 hx]
  obtain ⟨j, e, rfl⟩ := exists_coordinates (Nat.le_of_succ_le hn) f g
  rw [image_commute_reflection_iff hn f i j e, hz, image_rotation_mul,
    image_element_eq_one_iff, image_element_eq_iff, image_element_eq_iff,
    image_element_eq_iff]
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  constructor
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, Or.inr rfl⟩
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, Or.inr rfl⟩

theorem kleinFour_mul_comm (V : Subgroup S) [IsKleinFour V] {a b : S} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a :=
  congrArg Subtype.val
    (mul_comm_of_exponent_two IsKleinFour.exponent_two (⟨a, ha⟩ : V) ⟨b, hb⟩)

theorem kleinFour_orderOf (V : Subgroup S) [IsKleinFour V] {x : S} (hx : x ∈ V) (h1 : x ≠ 1) :
    orderOf x = 2 := by
  have hsq : (⟨x, hx⟩ : V) ^ 2 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : V)
    rwa [IsKleinFour.exponent_two] at h
  exact orderOf_eq_prime (congrArg Subtype.val hsq) h1

theorem kleinFour_eq_closure (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (V : Subgroup S)
    [IsKleinFour V] (x : S) (hxV : x ∈ V)
    (hxz : x ∉ Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2))) :
    V = Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 2), x} ∧
      Subgroup.centralizer (V : Set S) = V ∧ orderOf x = 2 := by
  have := finite_of_semidihedral (Nat.le_of_succ_le hn) f
  have hx2 : orderOf x = 2 :=
    kleinFour_orderOf V hxV fun h => hxz (h ▸ Subgroup.one_mem _)
  obtain ⟨hC, hK⟩ := centralizer_eq_closure hn f x hx2 hxz
  have hVC : V ≤ Subgroup.centralizer {x} := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (kleinFour_mul_comm V hg hxV)
  have hVeq : V = Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 2), x} := by
    rw [← hC]
    refine Subgroup.eq_of_le_of_card_ge hVC ?_
    rw [hC, IsKleinFour.card_four, IsKleinFour.card_four]
  refine ⟨hVeq, le_antisymm ?_ ?_, hx2⟩
  · calc Subgroup.centralizer (V : Set S) ≤ Subgroup.centralizer {x} :=
          Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxV)
      _ = V := by rw [hC, ← hVeq]
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact kleinFour_mul_comm V hh hg

theorem kleinFour_exists_not_mem (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (V : Subgroup S)
    [IsKleinFour V] : ∃ x ∈ V, x ∉ Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2)) := by
  have := finite_of_semidihedral (Nat.le_of_succ_le hn) f
  by_contra h
  have hle : V ≤ Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2)) := fun x hx =>
    by_contra fun hxz => h ⟨x, hx, hxz⟩
  have hcard := Subgroup.card_le_of_le hle
  rw [IsKleinFour.card_four, Nat.card_zpowers, image_z_orderOf (Nat.le_of_succ_le hn)] at hcard
  omega

end Centralizer

section Normalizer

theorem image_mem_closure_iff (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i j : ZMod (modulus n)) (hi : i.val % 2 = 0) (e : ZMod 2) :
    f (element n (Nat.le_of_succ_le hn) j e) ∈
        Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 2), f (element n (Nat.le_of_succ_le hn) i 1)} ↔
      (e = 0 ∧ (j = 0 ∨ j = (half n : ZMod (modulus n)))) ∨
        (e = 1 ∧ (j = i ∨ j = (half n : ZMod (modulus n)) + i)) := by
  have hxz : f (element n (Nat.le_of_succ_le hn) i 1) ∉
      Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2)) := fun h => by
      have hr : f (r n) ^ (2 ^ (n - 1) / 2) ∈ Subgroup.zpowers (f (r n)) :=
        Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      have := (Subgroup.zpowers_le.mpr hr) h
      rw [image_element_mem_zpowers_r_iff] at this
      exact absurd this (by decide)
  have hx2 : orderOf (f (element n (Nat.le_of_succ_le hn) i 1)) = 2 :=
    (image_reflection_orderOf_eq_two_iff (Nat.le_of_succ_le hn) f i).mpr hi
  rw [← (centralizer_eq_closure hn f _ hx2 hxz).1, Subgroup.mem_centralizer_singleton_iff,
    image_commute_reflection_iff hn f i j e]

theorem normalizer_closure (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S)
    (i : ZMod (modulus n)) (hi : i.val % 2 = 0) (K : Subgroup S)
    (hK : K = Subgroup.closure
      {f (r n) ^ (2 ^ (n - 1) / 2), f (element n (Nat.le_of_succ_le hn) i 1)}) :
    Subgroup.normalizer (K : Set S) =
        Subgroup.closure
          {f (r n) ^ (2 ^ (n - 1) / 4), f (element n (Nat.le_of_succ_le hn) i 1)} ∧
      Nonempty (Subgroup.normalizer (K : Set S) ≃* DihedralGroup 4) ∧
      Nat.card (Subgroup.normalizer (K : Set S)) = 8 := by
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  have := finite_of_semidihedral hn3 f
  set q : ZMod (modulus n) := ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) with hqdef
  set z := f (r n) ^ (2 ^ (n - 1) / 2) with hzdef
  set x := f (element n hn3 i 1) with hxdef
  have hzc : z ∈ Subgroup.center S := image_z_mem_center hn f
  have hz2 : orderOf z = 2 := image_z_orderOf hn3 f
  have hx2 : orderOf x = 2 := (image_reflection_orderOf_eq_two_iff hn3 f i).mpr hi
  have hmemK : ∀ (j : ZMod (modulus n)) (e : ZMod 2), f (element n hn3 j e) ∈ K ↔
      ((e = 0 ∧ (j = 0 ∨ j = (half n : ZMod (modulus n)))) ∨
        (e = 1 ∧ (j = i ∨ j = (half n : ZMod (modulus n)) + i))) := by
    intro j e
    rw [hK]
    exact image_mem_closure_iff hn f i j hi e
  have hfour : ∀ y : S, y ∈ K ↔ y = 1 ∨ y = z ∨ y = x ∨ y = z * x := by
    intro y
    rw [hK, closure_pair_eq_sup]
    exact KleinFourOddKernel.mem_fourSubgroup z x y hzc hz2 hx2
  have hzK : z ∈ K := (hfour z).mpr (Or.inr (Or.inl rfl))
  have hxK : x ∈ K := (hfour x).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hnorm : ∀ g : S, g ∈ Subgroup.normalizer (K : Set S) ↔ g * x * g⁻¹ ∈ K := by
    intro g
    constructor
    · intro hg
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp hxK
    · intro hg
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      have hcomm : g * z = z * g := Subgroup.mem_center_iff.mp hzc g
      rcases (hfour y).mp hy with rfl | rfl | rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact K.one_mem
      · rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hzK
      · exact hg
      · have h : g * (z * x) * g⁻¹ = z * (g * x * g⁻¹) := by
          rw [← mul_assoc g, hcomm]
          simp only [mul_assoc]
        rw [h]
        exact K.mul_mem hzK hg
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hcrit0 : ∀ j : ZMod (modulus n),
      f (element n hn3 j 0) ∈ Subgroup.normalizer (K : Set S) ↔ 4 * j = 0 := by
    intro j
    rw [hnorm, hxdef, ← map_inv, ← map_mul, ← map_mul, conjugate_reflection_by_rotation,
      hmemK, ← one_sub_twist_mul_mem_iff hn]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h | h⟩)
      · exact absurd h h10
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inr ⟨rfl, Or.inl (by linear_combination h)⟩
      · exact Or.inr ⟨rfl, Or.inr (by linear_combination h)⟩
  have hcrit1 : ∀ j : ZMod (modulus n),
      f (element n hn3 j 1) ∈ Subgroup.normalizer (K : Set S) ↔ 4 * (j - i) = 0 := by
    intro j
    rw [hnorm, hxdef, ← map_inv, ← map_mul, ← map_mul, conjugate_reflection_by_reflection,
      hmemK, ← one_sub_twist_mul_mem_iff hn]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h | h⟩)
      · exact absurd h h10
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inr ⟨rfl, Or.inl (by linear_combination h)⟩
      · exact Or.inr ⟨rfl, Or.inr (by linear_combination h)⟩
  have hρ : f (r n) ^ (2 ^ (n - 1) / 4) = f (element n hn3 q 0) := image_quarter_eq hn f
  have hρN : f (r n) ^ (2 ^ (n - 1) / 4) ∈ Subgroup.normalizer (K : Set S) := by
    rw [hρ, hcrit0]
    exact (four_mul_eq_zero_iff hn q).mpr ⟨1, by rw [Nat.cast_one, one_mul]⟩
  have hxN : x ∈ Subgroup.normalizer (K : Set S) := Subgroup.le_normalizer hxK
  have hrot : ∀ k : ZMod (modulus n), 4 * k = 0 →
      f (element n hn3 k 0) ∈ Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 4)) := by
    intro k hk
    obtain ⟨c, rfl⟩ := (four_mul_eq_zero_iff hn k).mp hk
    refine Subgroup.mem_zpowers_iff.mpr ⟨(c : ℤ), ?_⟩
    rw [zpow_natCast, hρ, ← map_pow, element_rotation_pow, nsmul_eq_mul]
  have hsub : Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 4)) ≤
      Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 4), x} :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
  have hclosure : Subgroup.normalizer (K : Set S) =
      Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 4), x} := by
    apply le_antisymm
    · intro g hg
      obtain ⟨j, e, rfl⟩ := exists_coordinates hn3 f g
      rcases exponent_cases e with rfl | rfl
      · rw [hcrit0] at hg
        exact hsub (hrot j hg)
      · rw [hcrit1] at hg
        have hprod : f (element n hn3 j 1) = f (element n hn3 (j - i) 0) * x := by
          rw [hxdef, image_rotation_mul, sub_add_cancel]
        rw [hprod]
        exact Subgroup.mul_mem _ (hsub (hrot _ hg))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · rw [Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact hρN
      · exact hxN
  refine ⟨hclosure, ?_⟩
  set N := Subgroup.normalizer (K : Set S) with hNdef
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : N, (ρ' : S) = f (r n) ^ (2 ^ (n - 1) / 4) := ⟨⟨_, hρN⟩, rfl⟩
  obtain ⟨σ', hσ'⟩ : ∃ σ' : N, (σ' : S) = x := ⟨⟨x, hxN⟩, rfl⟩
  have hgen : (⊤ : Subgroup N) = Subgroup.zpowers ρ' ⊔ Subgroup.zpowers σ' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, Subgroup.coe_subtype, hρ', hσ', hclosure, closure_pair_eq_sup]
  have hσ2 : σ' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hσ', ← hx2, pow_orderOf_eq_one]
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv, hρ', hσ', hρ,
      hxdef, ← map_inv, ← map_mul, ← map_mul, ← map_inv, conjugate_rotation_by_reflection,
      element_rotation_inv, twist_mul_quarter hn]
  have hσρ : σ' ∉ Subgroup.zpowers ρ' := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have hk' := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow, hρ', hσ'] at hk'
    have hmem : x ∈ Subgroup.zpowers (f (r n)) := by
      rw [← hk', ← zpow_natCast, ← zpow_mul]
      exact Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩
    rw [hxdef, image_element_mem_zpowers_r_iff] at hmem
    exact absurd hmem (by decide)
  have hρ4 : orderOf ρ' = 4 := by
    rw [← Subgroup.orderOf_coe, hρ', hρ, equiv_orderOf, rotation_order_four_iff n hn]
    exact Or.inl rfl
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ' σ' hgen hσ2 hrel hσρ
  rw [hρ4] at e
  refine ⟨⟨e⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem normalizer_kleinFour (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (V : Subgroup S)
    [IsKleinFour V] (x : S) (hxV : x ∈ V)
    (hxz : x ∉ Subgroup.zpowers (f (r n) ^ (2 ^ (n - 1) / 2))) :
    Subgroup.normalizer (V : Set S) = Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 4), x} ∧
      Nonempty (Subgroup.normalizer (V : Set S) ≃* DihedralGroup 4) ∧
      Nat.card (Subgroup.normalizer (V : Set S)) = 8 := by
  obtain ⟨hVeq, -, hx2⟩ := kleinFour_eq_closure hn f V x hxV hxz
  obtain ⟨i, hi, rfl⟩ := exists_reflection_coordinates hn f _ hx2 hxz
  exact normalizer_closure hn f i hi V hVeq

end Normalizer

section Conjugacy

theorem kleinFour_conj (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (V W : Subgroup S)
    [IsKleinFour V] [IsKleinFour W] :
    ∃ g ∈ Subgroup.zpowers (f (r n)), W = V.map (MulAut.conj g).toMonoidHom := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨x, hxV, hxz⟩ := kleinFour_exists_not_mem hn f V
  obtain ⟨y, hyW, hyz⟩ := kleinFour_exists_not_mem hn f W
  obtain ⟨hV, -, hx2⟩ := kleinFour_eq_closure hn f V x hxV hxz
  obtain ⟨hW, -, hy2⟩ := kleinFour_eq_closure hn f W y hyW hyz
  obtain ⟨i, hi, rfl⟩ := exists_reflection_coordinates hn f _ hx2 hxz
  obtain ⟨j, hj, rfl⟩ := exists_reflection_coordinates hn f _ hy2 hyz
  have heven : ∀ k : ZMod (modulus n), k.val % 2 = 0 →
      k = 2 * ((k.val / 2 : ℕ) : ZMod (modulus n)) := by
    intro k hk
    conv_lhs => rw [← ZMod.natCast_zmod_val k]
    rw [← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk), Nat.cast_mul, Nat.cast_ofNat,
      Nat.mul_div_cancel_left _ (by norm_num)]
  set c : ZMod (modulus n) := ((j.val / 2 : ℕ) : ZMod (modulus n)) -
    ((i.val / 2 : ℕ) : ZMod (modulus n)) with hc
  have hji : j - i = 2 * c := by
    rw [hc, mul_sub, ← heven j hj, ← heven i hi]
  obtain ⟨u, hu⟩ := quarter_sub_one_isUnit n hn
  have hmul : (1 - twist n) * (-(↑u⁻¹ * c)) = j - i := by
    have huinv : (u : ZMod (modulus n)) * ↑u⁻¹ = 1 := Units.mul_inv u
    rw [hji]
    linear_combination (↑u⁻¹ * c) * twist_sub_one_eq_two_mul n hn - (2 * c * ↑u⁻¹) * hu +
      (2 * c) * huinv
  set g := f (element n hn3 (-(↑u⁻¹ * c)) 0) with hg
  have hgr : g ∈ Subgroup.zpowers (f (r n)) :=
    (image_element_mem_zpowers_r_iff hn3 f _ _).mpr rfl
  refine ⟨g, hgr, ?_⟩
  have hzc := image_z_mem_center hn f
  have hgz : MulAut.conj g (f (r n) ^ (2 ^ (n - 1) / 2)) = f (r n) ^ (2 ^ (n - 1) / 2) := by
    rw [MulAut.conj_apply, (Subgroup.mem_center_iff.mp hzc g), mul_assoc, mul_inv_cancel,
      mul_one]
  have hgx : MulAut.conj g (f (element n hn3 i 1)) = f (element n hn3 j 1) := by
    rw [MulAut.conj_apply, hg, ← map_inv, ← map_mul, ← map_mul,
      conjugate_reflection_by_rotation, hmul, add_sub_cancel]
  rw [hV, hW, MonoidHom.map_closure, Set.image_pair]
  change Subgroup.closure {f (r n) ^ (2 ^ (n - 1) / 2), f (element n hn3 j 1)} =
    Subgroup.closure {MulAut.conj g (f (r n) ^ (2 ^ (n - 1) / 2)),
      MulAut.conj g (f (element n hn3 i 1))}
  rw [hgz, hgx]

end Conjugacy

theorem semidihedral_four_subgroup_centralizers (n : ℕ) (hn : 4 ≤ n)
    (f : SemidihedralGroup n ≃* S) :
    let r := f (CFSG.Semidihedral.r n)
    let m := 2 ^ (n - 1)
    let z := r ^ (m / 2)
    (∀ x : S, orderOf x = 2 → x ∉ Subgroup.zpowers z →
      Subgroup.centralizer {x} = Subgroup.closure {z, x} ∧
        IsKleinFour (Subgroup.closure {z, x})) ∧
    (∀ V : Subgroup S, IsKleinFour V →
      z ∈ V ∧ Subgroup.centralizer (V : Set S) = V ∧
        ∀ x ∈ V, x ∉ Subgroup.zpowers z →
          Subgroup.normalizer (V : Set S) = Subgroup.closure {r ^ (m / 4), x} ∧
          Nonempty (Subgroup.normalizer (V : Set S) ≃* DihedralGroup 4) ∧
          Nat.card (Subgroup.normalizer (V : Set S)) = 8) ∧
    (∀ V W : Subgroup S, IsKleinFour V → IsKleinFour W →
      ∃ g ∈ Subgroup.zpowers r, W = V.map (MulAut.conj g).toMonoidHom) := by
  intro r m z
  refine ⟨fun x hx hxz => centralizer_eq_closure hn f x hx hxz, fun V _ => ?_,
    fun V W _ _ => kleinFour_conj hn f V W⟩
  obtain ⟨x, hxV, hxz⟩ := kleinFour_exists_not_mem hn f V
  obtain ⟨hVeq, hC, -⟩ := kleinFour_eq_closure hn f V x hxV hxz
  refine ⟨by rw [hVeq]; exact Subgroup.subset_closure (Set.mem_insert _ _), hC,
    fun y hyV hyz => normalizer_kleinFour hn f V y hyV hyz⟩

end CFSG.Semidihedral.Local
