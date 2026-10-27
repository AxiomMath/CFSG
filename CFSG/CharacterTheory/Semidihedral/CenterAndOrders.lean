module

public import CFSG.CharacterTheory.Semidihedral.Subgroups
public import CFSG.CharacterTheory.Semidihedral.CoordinateLaws

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem half_eq_two_mul_quarter {n : ℕ} (hn : 3 ≤ n) :
    half n = 2 * 2 ^ (n - 3) := by
  have he : n - 2 = (n - 3) + 1 := by omega
  simp only [half, he, pow_succ]
  omega

theorem two_mul_half_residue (n : ℕ) (hn : 3 ≤ n) :
    2 * (half n : ZMod (modulus n)) = 0 := by
  calc
    2 * (half n : ZMod (modulus n)) = ((2 * half n : ℕ) : ZMod (modulus n)) := by
      push_cast
      rfl
    _ = (modulus n : ZMod (modulus n)) := by rw [modulus_eq_two_mul_half (by omega)]
    _ = 0 := ZMod.natCast_self _

theorem two_mul_eq_zero_iff (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) :
    2 * i = 0 ↔ i = 0 ∨ i = (half n : ZMod (modulus n)) := by
  have hp : 0 < half n := pow_pos (by decide) _
  have hlt := ZMod.val_lt i
  have heq : 2 * i = ((2 * i.val : ℕ) : ZMod (modulus n)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rfl
  have hdiv (t : ℕ) : modulus n ∣ 2 * t ↔ half n ∣ t := by
    rw [modulus_eq_two_mul_half (by omega),
      Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))]
  rw [heq, ZMod.natCast_eq_zero_iff, hdiv]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    have hbound : a < 2 := by
      rw [ha, modulus_eq_two_mul_half (by omega)] at hlt
      nlinarith
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · left
      apply ZMod.val_injective
      simpa using ha
    · right
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt (by rw [modulus_eq_two_mul_half (by omega)]; omega)]
      simpa using ha
  · rintro (rfl | rfl)
    · simp
    · rw [ZMod.val_natCast_of_lt (by rw [modulus_eq_two_mul_half (by omega)]; omega)]

theorem half_residue_ne_zero (n : ℕ) (hn : 3 ≤ n) :
    (half n : ZMod (modulus n)) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  have hp : 0 < half n := pow_pos (by decide) _
  rw [ZMod.val_natCast_of_lt (by rw [modulus_eq_two_mul_half (by omega)]; omega),
    ZMod.val_zero] at hv
  omega

theorem twist_sub_one_eq_two_mul (n : ℕ) (hn : 4 ≤ n) :
    twist n - 1 = 2 * ((2 ^ (n - 3) - 1 : ℕ) : ZMod (modulus n)) := by
  have hp : 1 ≤ 2 ^ (n - 3) := Nat.succ_le_of_lt (pow_pos (by decide) _)
  rw [twist, half_eq_two_mul_quarter (by omega), Nat.cast_mul,
    Nat.cast_sub hp, Nat.cast_one]
  ring

theorem quarter_sub_one_isUnit (n : ℕ) (hn : 4 ≤ n) :
    IsUnit ((2 ^ (n - 3) - 1 : ℕ) : ZMod (modulus n)) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_two_right]
  have he : n - 3 = (n - 4) + 1 := by omega
  have hpos : 0 < 2 ^ (n - 4) := pow_pos (by decide) _
  refine ⟨2 ^ (n - 4) - 1, ?_⟩
  rw [he, pow_succ]
  omega

theorem twist_fixed_iff (n : ℕ) (hn : 4 ≤ n) (i : ZMod (modulus n)) :
    twist n * i = i ↔ i = 0 ∨ i = (half n : ZMod (modulus n)) := by
  rw [← sub_eq_zero]
  have heq : twist n * i - i =
      ((2 ^ (n - 3) - 1 : ℕ) : ZMod (modulus n)) * (2 * i) := by
    calc
      twist n * i - i = (twist n - 1) * i := by ring
      _ = _ := by rw [twist_sub_one_eq_two_mul n hn]; ring
  rw [heq, (quarter_sub_one_isUnit n hn).mul_right_eq_zero,
    two_mul_eq_zero_iff n (by omega)]

theorem twist_ne_one (n : ℕ) (hn : 4 ≤ n) : twist n ≠ 1 := by
  intro h
  have hf := (twist_fixed_iff n hn 1).mp (by simpa using h)
  rcases hf with h | h
  · have hv := congrArg (fun x : ZMod (modulus n) => x.val) h
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by
      have hm := modulus_two_le (by omega : 2 ≤ n)
      omega), ZMod.val_zero] at hv
    omega
  · have hp : 2 ≤ half n := by
      rw [half_eq_two_mul_quarter (by omega)]
      have hq : 0 < 2 ^ (n - 3) := pow_pos (by decide) _
      omega
    have hv := congrArg (fun x : ZMod (modulus n) => x.val) h
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by
      have hm := modulus_two_le (by omega : 2 ≤ n)
      omega), ZMod.val_natCast_of_lt (by
      rw [modulus_eq_two_mul_half (by omega)]; omega)] at hv
    omega

theorem element_mem_center_iff (n : ℕ) (hn : 4 ≤ n)
    (i : ZMod (modulus n)) (e : ZMod 2) :
    element n (by omega) i e ∈ Subgroup.center (SemidihedralGroup n) ↔
      e = 0 ∧ (i = 0 ∨ i = (half n : ZMod (modulus n))) := by
  constructor
  · intro hz
    have hr := Subgroup.mem_center_iff.mp hz (r n)
    have hs := Subgroup.mem_center_iff.mp hz (s n)
    have hrcoord : r n = element n (by omega) 1 0 := by
      simpa only [pow_one, Nat.cast_one] using r_pow_eq_element n (by omega) 1
    rw [hrcoord] at hr
    rw [s_eq_element n (by omega)] at hs
    rcases exponent_cases e with rfl | rfl
    · refine ⟨rfl, (twist_fixed_iff n hn i).mp ?_⟩
      rw [element_reflection_mul, element_rotation_mul, add_zero,
        element_eq_iff] at hs
      simpa only [zero_add, add_zero] using hs.1
    · rw [element_rotation_mul, element_reflection_mul, mul_one,
        element_eq_iff] at hr
      have ht : twist n = 1 := by linear_combination -hr.1
      exact False.elim (twist_ne_one n hn ht)
  · rintro ⟨rfl, hi⟩
    have hfix := (twist_fixed_iff n hn i).mpr hi
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨⟨j, f⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective g
    change element n (by omega) j f * element n (by omega) i 0 =
      element n (by omega) i 0 * element n (by omega) j f
    rcases exponent_cases f with rfl | rfl
    · rw [element_rotation_mul, element_rotation_mul, add_comm]
    · rw [element_reflection_mul, element_rotation_mul, add_zero, hfix, add_comm]

theorem z_eq_element (n : ℕ) (hn : 3 ≤ n) :
    z n = element n hn (half n : ZMod (modulus n)) 0 :=
  r_pow_eq_element n hn (half n)

theorem z_sq (n : ℕ) (hn : 3 ≤ n) : z n ^ 2 = 1 := by
  rw [z_eq_element n hn, element_rotation_pow, nsmul_eq_mul,
    Nat.cast_ofNat, two_mul_half_residue n hn, element_zero_zero]

theorem z_ne_one (n : ℕ) (hn : 3 ≤ n) : z n ≠ 1 := by
  rw [z_eq_element n hn, ne_eq, element_eq_one_iff]
  exact fun h => half_residue_ne_zero n hn h.1

theorem orderOf_z (n : ℕ) (hn : 3 ≤ n) : orderOf (z n) = 2 := by
  rw [orderOf_eq_prime_iff]
  exact ⟨z_sq n hn, z_ne_one n hn⟩

theorem z_mem_center (n : ℕ) (hn : 4 ≤ n) :
    z n ∈ Subgroup.center (SemidihedralGroup n) := by
  rw [z_eq_element n (by omega), element_mem_center_iff n hn]
  exact ⟨rfl, Or.inr rfl⟩

theorem center_eq_zpowers (n : ℕ) (hn : 4 ≤ n) :
    Subgroup.center (SemidihedralGroup n) = Subgroup.zpowers (z n) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective g
    change element n (by omega) i e ∈ Subgroup.center _ at hg
    change element n (by omega) i e ∈ Subgroup.zpowers (z n)
    rcases (element_mem_center_iff n hn i e).mp hg with ⟨rfl, rfl | rfl⟩
    · rw [element_zero_zero]
      exact (Subgroup.zpowers (z n)).one_mem
    · rw [← z_eq_element n (by omega)]
      exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (z_mem_center n hn)

theorem center_card (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (Subgroup.center (SemidihedralGroup n)) = 2 := by
  rw [center_eq_zpowers n hn, Nat.card_zpowers, orderOf_z n (by omega)]

theorem rotation_involution_iff (n : ℕ) (hn : 3 ≤ n)
    (i : ZMod (modulus n)) :
    orderOf (element n hn i 0) = 2 ↔ i = (half n : ZMod (modulus n)) := by
  rw [orderOf_eq_prime_iff, element_rotation_pow, nsmul_eq_mul,
    element_eq_one_iff, Nat.cast_ofNat, two_mul_eq_zero_iff n hn]
  rw [ne_eq, element_eq_one_iff]
  simp only [eq_self, and_true]
  constructor
  · rintro ⟨h, hne⟩
    exact h.resolve_left hne
  · intro h
    exact ⟨Or.inr h, h.symm ▸ half_residue_ne_zero n hn⟩

end CFSG.Semidihedral
