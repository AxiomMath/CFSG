module

public import CFSG.CharacterTheory.Semidihedral.Subgroups
public import CFSG.CharacterTheory.Semidihedral.CoordinateLaws

public section

namespace CFSG.Semidihedral

open CFSG.Open

namespace DihedralQuaternion

instance halfNeZero (n : ℕ) : NeZero (half n) :=
  ⟨pow_ne_zero _ (by decide)⟩

instance parameterNeZero (n : ℕ) : NeZero (2 ^ (n - 3)) :=
  ⟨pow_ne_zero _ (by decide)⟩

theorem half_eq_two_mul_parameter (n : ℕ) (hn : 3 ≤ n) :
    half n = 2 * 2 ^ (n - 3) := by
  have he : n - 2 = (n - 3) + 1 := by omega
  simp only [half, he, pow_succ]
  omega

theorem modulus_eq_four_mul_parameter (n : ℕ) (hn : 3 ≤ n) :
    modulus n = 2 * (2 * 2 ^ (n - 3)) := by
  rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_parameter n hn]

@[expose] def doubleCoordinate (d m : ℕ) [NeZero d] (hm : m = 2 * d) :
    ZMod d →+ ZMod m where
  toFun a := ((2 * a.val : ℕ) : ZMod m)
  map_zero' := by simp
  map_add' a b := by
    simp only [ZMod.val_add]
    calc
      ((2 * ((a.val + b.val) % d) : ℕ) : ZMod m) =
          (((2 * (a.val + b.val)) % m : ℕ) : ZMod m) := by
        rw [hm, Nat.mul_mod_mul_left]
      _ = ((2 * (a.val + b.val) : ℕ) : ZMod m) := ZMod.natCast_mod _ _
      _ = ((2 * a.val : ℕ) : ZMod m) + ((2 * b.val : ℕ) : ZMod m) := by
        push_cast
        ring

@[simp] theorem doubleCoordinate_natCast (d m : ℕ) [NeZero d] (hm : m = 2 * d)
    (a : ℕ) : doubleCoordinate d m hm (a : ZMod d) = 2 * (a : ZMod m) := by
  change ((2 * (a : ZMod d).val : ℕ) : ZMod m) = _
  rw [ZMod.val_natCast]
  rw [← Nat.mul_mod_mul_left, ← hm, ZMod.natCast_mod]
  push_cast
  rfl

theorem doubleCoordinate_val (d m : ℕ) [NeZero d] [NeZero m] (hm : m = 2 * d)
    (a : ZMod d) : (doubleCoordinate d m hm a).val = 2 * a.val := by
  change ((2 * a.val : ℕ) : ZMod m).val = _
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  rw [hm]
  exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) (by decide)

theorem doubleCoordinate_injective (d m : ℕ) [NeZero d] [NeZero m]
    (hm : m = 2 * d) : Function.Injective (doubleCoordinate d m hm) := by
  intro a b hab
  have hv := congrArg ZMod.val hab
  rw [doubleCoordinate_val, doubleCoordinate_val] at hv
  apply ZMod.val_injective
  omega

theorem twist_mul_two (n : ℕ) (hn : 3 ≤ n) :
    twist n * (2 : ZMod (modulus n)) = -2 := by
  have hhalf : (half n : ZMod (modulus n)) * 2 = 0 := by
    calc
      (half n : ZMod (modulus n)) * 2 = ((2 * half n : ℕ) : ZMod (modulus n)) := by
        push_cast
        ring
      _ = (modulus n : ZMod (modulus n)) := by
        rw [modulus_eq_two_mul_half (by omega)]
      _ = 0 := ZMod.natCast_self _
  simp only [twist, sub_mul, one_mul, hhalf, zero_sub]

theorem twist_doubleCoordinate (n d : ℕ) (hn : 3 ≤ n) [NeZero d]
    (hm : modulus n = 2 * d) (a : ZMod d) :
    twist n * doubleCoordinate d (modulus n) hm a =
      -doubleCoordinate d (modulus n) hm a := by
  change twist n * ((2 * a.val : ℕ) : ZMod (modulus n)) =
    -((2 * a.val : ℕ) : ZMod (modulus n))
  push_cast
  rw [← mul_assoc, twist_mul_two n hn]
  ring

@[expose] def dihedralCoordinate (n : ℕ) (hn : 4 ≤ n) :
    ZMod (half n) →+ ZMod (modulus n) :=
  doubleCoordinate (half n) (modulus n) (modulus_eq_two_mul_half (by omega))

@[expose] def quaternionCoordinate (n : ℕ) (hn : 4 ≤ n) :
    ZMod (2 * 2 ^ (n - 3)) →+ ZMod (modulus n) :=
  doubleCoordinate (2 * 2 ^ (n - 3)) (modulus n)
    (modulus_eq_four_mul_parameter n (by omega))

@[simp] theorem dihedralCoordinate_one (n : ℕ) (hn : 4 ≤ n) :
    dihedralCoordinate n hn 1 = 2 := by
  simpa only [dihedralCoordinate, Nat.cast_one, mul_one] using
    doubleCoordinate_natCast (half n) (modulus n) (modulus_eq_two_mul_half (by omega)) 1

@[simp] theorem quaternionCoordinate_one (n : ℕ) (hn : 4 ≤ n) :
    quaternionCoordinate n hn 1 = 2 := by
  simpa only [quaternionCoordinate, Nat.cast_one, mul_one] using
    doubleCoordinate_natCast (2 * 2 ^ (n - 3)) (modulus n)
      (modulus_eq_four_mul_parameter n (by omega)) 1

theorem quaternionCoordinate_parameter (n : ℕ) (hn : 4 ≤ n) :
    quaternionCoordinate n hn (2 ^ (n - 3) : ℕ) = (half n : ZMod (modulus n)) := by
  change doubleCoordinate _ _ _ _ = _
  rw [doubleCoordinate_natCast, half_eq_two_mul_parameter n (by omega), Nat.cast_mul]
  rfl

theorem dihedralCoordinate_twist (n : ℕ) (hn : 4 ≤ n) (a : ZMod (half n)) :
    twist n * dihedralCoordinate n hn a = -dihedralCoordinate n hn a :=
  twist_doubleCoordinate n (half n) (by omega) (modulus_eq_two_mul_half (by omega)) a

theorem quaternionCoordinate_twist (n : ℕ) (hn : 4 ≤ n)
    (a : ZMod (2 * 2 ^ (n - 3))) :
    twist n * quaternionCoordinate n hn a = -quaternionCoordinate n hn a :=
  twist_doubleCoordinate n _ (by omega) (modulus_eq_four_mul_parameter n (by omega)) a

end DihedralQuaternion

open DihedralQuaternion

@[expose] def dihedralHom (n : ℕ) (hn : 4 ≤ n) :
    DihedralGroup (half n) →* SemidihedralGroup n where
  toFun
    | DihedralGroup.r a => element n (by omega) (dihedralCoordinate n hn a) 0
    | DihedralGroup.sr a => element n (by omega) (-dihedralCoordinate n hn a) 1
  map_one' := by
    change element n (by omega) (dihedralCoordinate n hn 0) 0 = 1
    rw [map_zero, element_zero_zero]
  map_mul' := by
    rintro (a | a) (b | b)
    · change element n (by omega) (dihedralCoordinate n hn (a + b)) 0 =
        element n (by omega) (dihedralCoordinate n hn a) 0 *
          element n (by omega) (dihedralCoordinate n hn b) 0
      rw [element_rotation_mul, map_add]
    · change element n (by omega) (-dihedralCoordinate n hn (b - a)) 1 =
        element n (by omega) (dihedralCoordinate n hn a) 0 *
          element n (by omega) (-dihedralCoordinate n hn b) 1
      rw [element_rotation_mul, map_sub]
      congr 1
      ring
    · change element n (by omega) (-dihedralCoordinate n hn (a + b)) 1 =
        element n (by omega) (-dihedralCoordinate n hn a) 1 *
          element n (by omega) (dihedralCoordinate n hn b) 0
      rw [element_reflection_mul, dihedralCoordinate_twist, map_add, add_zero]
      congr 1
      ring
    · change element n (by omega) (dihedralCoordinate n hn (b - a)) 0 =
        element n (by omega) (-dihedralCoordinate n hn a) 1 *
          element n (by omega) (-dihedralCoordinate n hn b) 1
      rw [element_reflection_mul, mul_neg, dihedralCoordinate_twist,
        show (1 + 1 : ZMod 2) = 0 by decide, map_sub]
      congr 1
      ring

@[expose] def quaternionHom (n : ℕ) (hn : 4 ≤ n) :
    QuaternionGroup (2 ^ (n - 3)) →* SemidihedralGroup n where
  toFun
    | QuaternionGroup.a a => element n (by omega) (quaternionCoordinate n hn a) 0
    | QuaternionGroup.xa a => element n (by omega) (1 - quaternionCoordinate n hn a) 1
  map_one' := by
    change element n (by omega) (quaternionCoordinate n hn 0) 0 = 1
    rw [map_zero, element_zero_zero]
  map_mul' := by
    rintro (a | a) (b | b)
    · change element n (by omega) (quaternionCoordinate n hn (a + b)) 0 =
        element n (by omega) (quaternionCoordinate n hn a) 0 *
          element n (by omega) (quaternionCoordinate n hn b) 0
      rw [element_rotation_mul, map_add]
    · change element n (by omega) (1 - quaternionCoordinate n hn (b - a)) 1 =
        element n (by omega) (quaternionCoordinate n hn a) 0 *
          element n (by omega) (1 - quaternionCoordinate n hn b) 1
      rw [element_rotation_mul, map_sub]
      congr 1
      ring
    · change element n (by omega) (1 - quaternionCoordinate n hn (a + b)) 1 =
        element n (by omega) (1 - quaternionCoordinate n hn a) 1 *
          element n (by omega) (quaternionCoordinate n hn b) 0
      rw [element_reflection_mul, quaternionCoordinate_twist, map_add, add_zero]
      congr 1
      ring
    · change element n (by omega)
          (quaternionCoordinate n hn ((2 ^ (n - 3) : ℕ) + b - a)) 0 =
        element n (by omega) (1 - quaternionCoordinate n hn a) 1 *
          element n (by omega) (1 - quaternionCoordinate n hn b) 1
      rw [element_reflection_mul, mul_sub, mul_one, quaternionCoordinate_twist,
        show (1 + 1 : ZMod 2) = 0 by decide, map_sub, map_add,
        quaternionCoordinate_parameter]
      congr 1
      simp only [twist]
      ring

@[simp] theorem dihedralHom_r (n : ℕ) (hn : 4 ≤ n) (a : ZMod (half n)) :
    dihedralHom n hn (DihedralGroup.r a) =
      element n (by omega) (dihedralCoordinate n hn a) 0 := rfl

@[simp] theorem dihedralHom_sr (n : ℕ) (hn : 4 ≤ n) (a : ZMod (half n)) :
    dihedralHom n hn (DihedralGroup.sr a) =
      element n (by omega) (-dihedralCoordinate n hn a) 1 := rfl

@[simp] theorem quaternionHom_a (n : ℕ) (hn : 4 ≤ n)
    (a : ZMod (2 * 2 ^ (n - 3))) :
    quaternionHom n hn (QuaternionGroup.a a) =
      element n (by omega) (quaternionCoordinate n hn a) 0 := rfl

@[simp] theorem quaternionHom_xa (n : ℕ) (hn : 4 ≤ n)
    (a : ZMod (2 * 2 ^ (n - 3))) :
    quaternionHom n hn (QuaternionGroup.xa a) =
      element n (by omega) (1 - quaternionCoordinate n hn a) 1 := rfl

@[simp] theorem dihedralHom_rotation (n : ℕ) (hn : 4 ≤ n) :
    dihedralHom n hn (DihedralGroup.r 1) = r n ^ 2 := by
  rw [dihedralHom_r, dihedralCoordinate_one, r_pow_eq_element n (by omega)]
  rfl

@[simp] theorem dihedralHom_reflection (n : ℕ) (hn : 4 ≤ n) :
    dihedralHom n hn (DihedralGroup.sr 0) = s n := by
  rw [dihedralHom_sr, map_zero, neg_zero, s_eq_element n (by omega)]

@[simp] theorem quaternionHom_rotation (n : ℕ) (hn : 4 ≤ n) :
    quaternionHom n hn (QuaternionGroup.a 1) = r n ^ 2 := by
  rw [quaternionHom_a, quaternionCoordinate_one, r_pow_eq_element n (by omega)]
  rfl

@[simp] theorem quaternionHom_generator (n : ℕ) (hn : 4 ≤ n) :
    quaternionHom n hn (QuaternionGroup.xa 0) = r n * s n := by
  have hr : r n = element n (by omega) 1 0 := by
    simpa only [pow_one, Nat.cast_one] using r_pow_eq_element n (by omega) 1
  rw [quaternionHom_xa, map_zero, sub_zero, hr, s_eq_element n (by omega),
    element_rotation_mul, add_zero]

theorem dihedralHom_injective (n : ℕ) (hn : 4 ≤ n) :
    Function.Injective (dihedralHom n hn) := by
  apply (injective_iff_map_eq_one (dihedralHom n hn)).mpr
  rintro (a | a) ha
  · rw [dihedralHom_r, element_eq_one_iff] at ha
    have hzero : a = 0 := by
      apply doubleCoordinate_injective (half n) (modulus n)
        (modulus_eq_two_mul_half (by omega))
      change dihedralCoordinate n hn a = dihedralCoordinate n hn 0
      rw [map_zero]
      exact ha.1
    simp only [hzero, DihedralGroup.r_zero]
  · rw [dihedralHom_sr, element_eq_one_iff] at ha
    exact (one_ne_zero ha.2).elim

theorem quaternionHom_injective (n : ℕ) (hn : 4 ≤ n) :
    Function.Injective (quaternionHom n hn) := by
  apply (injective_iff_map_eq_one (quaternionHom n hn)).mpr
  rintro (a | a) ha
  · rw [quaternionHom_a, element_eq_one_iff] at ha
    have hzero : a = 0 := by
      apply doubleCoordinate_injective (2 * 2 ^ (n - 3)) (modulus n)
        (modulus_eq_four_mul_parameter n (by omega))
      change quaternionCoordinate n hn a = quaternionCoordinate n hn 0
      rw [map_zero]
      exact ha.1
    simp only [hzero, QuaternionGroup.a_zero]
  · rw [quaternionHom_xa, element_eq_one_iff] at ha
    exact (one_ne_zero ha.2).elim

theorem dihedralHom_mem (n : ℕ) (hn : 4 ≤ n) (g : DihedralGroup (half n)) :
    dihedralHom n hn g ∈ dihedralSubgroup n := by
  have hr : r n ^ 2 ∈ dihedralSubgroup n :=
    Subgroup.subset_closure (by simp)
  have hs : s n ∈ dihedralSubgroup n :=
    Subgroup.subset_closure (by simp)
  cases g with
  | r a =>
    have he : DihedralGroup.r a = (DihedralGroup.r 1) ^ a.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [he, map_pow, dihedralHom_rotation]
    exact Subgroup.pow_mem _ hr _
  | sr a =>
    have he : DihedralGroup.sr a = DihedralGroup.sr 0 * (DihedralGroup.r 1) ^ a.val := by
      rw [DihedralGroup.r_one_pow, DihedralGroup.sr_mul_r, zero_add,
        ZMod.natCast_zmod_val]
    rw [he, map_mul, map_pow, dihedralHom_reflection, dihedralHom_rotation]
    exact Subgroup.mul_mem _ hs (Subgroup.pow_mem _ hr _)

theorem quaternionHom_mem (n : ℕ) (hn : 4 ≤ n)
    (g : QuaternionGroup (2 ^ (n - 3))) :
    quaternionHom n hn g ∈ quaternionSubgroup n := by
  have hr : r n ^ 2 ∈ quaternionSubgroup n :=
    Subgroup.subset_closure (by simp)
  have hx : r n * s n ∈ quaternionSubgroup n :=
    Subgroup.subset_closure (by simp)
  cases g with
  | a a =>
    have he : QuaternionGroup.a a = (QuaternionGroup.a 1) ^ a.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [he, map_pow, quaternionHom_rotation]
    exact Subgroup.pow_mem _ hr _
  | xa a =>
    have he : QuaternionGroup.xa a = QuaternionGroup.xa 0 *
        (QuaternionGroup.a 1) ^ a.val := by
      rw [QuaternionGroup.a_one_pow, QuaternionGroup.xa_mul_a, zero_add,
        ZMod.natCast_zmod_val]
    rw [he, map_mul, map_pow, quaternionHom_generator, quaternionHom_rotation]
    exact Subgroup.mul_mem _ hx (Subgroup.pow_mem _ hr _)

theorem dihedralHom_range (n : ℕ) (hn : 4 ≤ n) :
    (dihedralHom n hn).range = dihedralSubgroup n := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact dihedralHom_mem n hn g
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨DihedralGroup.r 1, dihedralHom_rotation n hn⟩
    · exact ⟨DihedralGroup.sr 0, dihedralHom_reflection n hn⟩

theorem quaternionHom_range (n : ℕ) (hn : 4 ≤ n) :
    (quaternionHom n hn).range = quaternionSubgroup n := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact quaternionHom_mem n hn g
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨QuaternionGroup.a 1, quaternionHom_rotation n hn⟩
    · exact ⟨QuaternionGroup.xa 0, quaternionHom_generator n hn⟩

@[expose] noncomputable def dihedralEquiv (n : ℕ) (hn : 4 ≤ n) :
    DihedralGroup (half n) ≃* dihedralSubgroup n :=
  (MonoidHom.ofInjective (dihedralHom_injective n hn)).trans
    (MulEquiv.subgroupCongr (dihedralHom_range n hn))

@[expose] noncomputable def quaternionEquiv (n : ℕ) (hn : 4 ≤ n) :
    QuaternionGroup (2 ^ (n - 3)) ≃* quaternionSubgroup n :=
  (MonoidHom.ofInjective (quaternionHom_injective n hn)).trans
    (MulEquiv.subgroupCongr (quaternionHom_range n hn))

@[simp] theorem dihedralEquiv_coe (n : ℕ) (hn : 4 ≤ n) (g : DihedralGroup (half n)) :
    (dihedralEquiv n hn g : SemidihedralGroup n) = dihedralHom n hn g := rfl

@[simp] theorem quaternionEquiv_coe (n : ℕ) (hn : 4 ≤ n)
    (g : QuaternionGroup (2 ^ (n - 3))) :
    (quaternionEquiv n hn g : SemidihedralGroup n) = quaternionHom n hn g := rfl

@[simp] theorem dihedralEquiv_rotation (n : ℕ) (hn : 4 ≤ n) :
    (dihedralEquiv n hn (DihedralGroup.r 1) : SemidihedralGroup n) = r n ^ 2 := by
  rw [dihedralEquiv_coe, dihedralHom_rotation]

@[simp] theorem dihedralEquiv_reflection (n : ℕ) (hn : 4 ≤ n) :
    (dihedralEquiv n hn (DihedralGroup.sr 0) : SemidihedralGroup n) = s n := by
  rw [dihedralEquiv_coe, dihedralHom_reflection]

@[simp] theorem quaternionEquiv_rotation (n : ℕ) (hn : 4 ≤ n) :
    (quaternionEquiv n hn (QuaternionGroup.a 1) : SemidihedralGroup n) = r n ^ 2 := by
  rw [quaternionEquiv_coe, quaternionHom_rotation]

@[simp] theorem quaternionEquiv_generator (n : ℕ) (hn : 4 ≤ n) :
    (quaternionEquiv n hn (QuaternionGroup.xa 0) : SemidihedralGroup n) = r n * s n := by
  rw [quaternionEquiv_coe, quaternionHom_generator]

theorem dihedralSubgroup_card (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (dihedralSubgroup n) = modulus n := by
  rw [← Nat.card_congr (dihedralEquiv n hn).toEquiv, DihedralGroup.nat_card,
    modulus_eq_two_mul_half (by omega)]

theorem quaternionSubgroup_card (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (quaternionSubgroup n) = modulus n := by
  rw [← Nat.card_congr (quaternionEquiv n hn).toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card, modulus_eq_four_mul_parameter n (by omega)]
  ring

theorem distinguished_dihedral_quaternion (n : ℕ) (hn : 4 ≤ n) :
    ∃ (d : DihedralGroup (half n) ≃* dihedralSubgroup n)
      (q : QuaternionGroup (2 ^ (n - 3)) ≃* quaternionSubgroup n),
      (d (DihedralGroup.r 1) : SemidihedralGroup n) = r n ^ 2 ∧
      (d (DihedralGroup.sr 0) : SemidihedralGroup n) = s n ∧
      (q (QuaternionGroup.a 1) : SemidihedralGroup n) = r n ^ 2 ∧
      (q (QuaternionGroup.xa 0) : SemidihedralGroup n) = r n * s n ∧
      Nat.card (dihedralSubgroup n) = modulus n ∧
      Nat.card (quaternionSubgroup n) = modulus n := by
  exact ⟨dihedralEquiv n hn, quaternionEquiv n hn, dihedralEquiv_rotation n hn,
    dihedralEquiv_reflection n hn, quaternionEquiv_rotation n hn,
    quaternionEquiv_generator n hn, dihedralSubgroup_card n hn,
    quaternionSubgroup_card n hn⟩

end CFSG.Semidihedral
