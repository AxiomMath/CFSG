module

public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem r_zpow_eq_element (n : ℕ) (hn : 3 ≤ n) (k : ℤ) :
    r n ^ k = element n hn (k : ZMod (modulus n)) 0 := by
  apply (presentationEquivModel n hn).injective
  change toModel n hn (r n ^ k) = toModel n hn (element n hn (k : ZMod (modulus n)) 0)
  rw [map_zpow, toModel_r, modelR, ← map_zpow, toModel_element]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change k • (1 : ZMod (modulus n)) = (k : ZMod (modulus n))
    simp
  · rfl

theorem z_zpow_eq_element (n : ℕ) (hn : 3 ≤ n) (k : ℤ) :
    z n ^ k = element n hn ((half n : ZMod (modulus n)) * k) 0 := by
  rw [z, ← zpow_natCast, ← zpow_mul, r_zpow_eq_element]
  push_cast
  rfl

theorem reflection_zpow_square (n : ℕ) (hn : 3 ≤ n) (i : ℤ) :
    (r n ^ i * s n) ^ 2 = z n ^ i := by
  rw [r_zpow_eq_element n hn, s_eq_element n hn, element_rotation_mul,
    add_zero, element_reflection_sq, z_zpow_eq_element]

theorem reflection_square_nat (n : ℕ) (hn : 3 ≤ n) (i : ℕ) :
    (r n ^ i * s n) ^ 2 = z n ^ i := by
  simpa only [zpow_natCast] using reflection_zpow_square n hn (i : ℤ)

theorem half_mul_residue (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) :
    (half n : ZMod (modulus n)) * i =
      ((half n * (i.val % 2) : ℕ) : ZMod (modulus n)) := by
  have hzero := two_mul_half_residue n hn
  have hdecomp := Nat.mod_add_div i.val 2
  have hcast : (i.val : ZMod (modulus n)) =
      (i.val % 2 : ℕ) + 2 * ((i.val / 2 : ℕ) : ZMod (modulus n)) := by
    calc
      (i.val : ZMod (modulus n)) =
          ((i.val % 2 + 2 * (i.val / 2) : ℕ) : ZMod (modulus n)) :=
        congrArg (fun t : ℕ => (t : ZMod (modulus n))) hdecomp.symm
      _ = _ := by push_cast; rfl
  calc
    (half n : ZMod (modulus n)) * i =
        (half n : ZMod (modulus n)) * (i.val : ZMod (modulus n)) := by
      rw [ZMod.natCast_zmod_val]
    _ = (half n : ZMod (modulus n)) *
        ((i.val % 2 : ℕ) + 2 * ((i.val / 2 : ℕ) : ZMod (modulus n))) := by
      rw [hcast]
    _ =
      (half n : ZMod (modulus n)) * (i.val % 2 : ℕ) +
        (2 * (half n : ZMod (modulus n))) * (i.val / 2 : ℕ) := by ring
    _ = _ := by rw [hzero]; push_cast; ring

theorem half_mul_eq_zero_iff (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) :
    (half n : ZMod (modulus n)) * i = 0 ↔ i.val % 2 = 0 := by
  rw [half_mul_residue n hn]
  have hm := Nat.mod_lt i.val (by decide : 0 < (2 : ℕ))
  have hcases : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hcases with h | h
  · simp [h]
  · simp [h, half_residue_ne_zero n hn]

theorem half_mul_eq_half_iff (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) :
    (half n : ZMod (modulus n)) * i = (half n : ZMod (modulus n)) ↔
      i.val % 2 = 1 := by
  rw [half_mul_residue n hn]
  have hm := Nat.mod_lt i.val (by decide : 0 < (2 : ℕ))
  have hcases : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hcases with h | h
  · simp [h, Ne.symm (half_residue_ne_zero n hn)]
  · simp [h]

theorem outside_involution_iff (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) :
    orderOf (element n hn i 1) = 2 ↔ i.val % 2 = 0 := by
  have hne : element n hn i 1 ≠ 1 := by simp
  rw [orderOf_eq_prime_iff, element_reflection_sq, element_eq_one_iff,
    half_mul_eq_zero_iff n hn]
  simp [hne]

theorem outside_order_four_iff (n : ℕ) (hn : 3 ≤ n) (i : ZMod (modulus n)) :
    orderOf (element n hn i 1) = 4 ↔ i.val % 2 = 1 := by
  constructor
  · intro ho
    have hne : element n hn i 1 ^ 2 ≠ 1 := by
      intro h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [ho] at hd
      omega
    have hnot : i.val % 2 ≠ 0 := by
      intro hi
      apply hne
      rw [element_reflection_sq, (half_mul_eq_zero_iff n hn i).mpr hi,
        element_zero_zero]
    have hm := Nat.mod_lt i.val (by decide : 0 < (2 : ℕ))
    omega
  · intro hi
    have hs : element n hn i 1 ^ 2 = z n := by
      rw [element_reflection_sq, (half_mul_eq_half_iff n hn i).mpr hi,
        ← z_eq_element n hn]
    have hsq : element n hn i 1 ^ 2 ≠ 1 := by rw [hs]; exact z_ne_one n hn
    have hfour : element n hn i 1 ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs, z_sq n hn]
    have ho := orderOf_eq_prime_pow (x := element n hn i 1) (n := 1) (p := 2)
      (by simpa using hsq) (by simpa using hfour)
    simpa using ho

theorem r_zpow_mul_s_ne_one (n : ℕ) (hn : 3 ≤ n) (i : ℤ) :
    r n ^ i * s n ≠ 1 := by
  rw [r_zpow_eq_element n hn, s_eq_element n hn, element_rotation_mul, add_zero]
  simp

theorem even_reflection_order (n : ℕ) (hn : 3 ≤ n) (j : ℤ) :
    orderOf (r n ^ (2 * j) * s n) = 2 := by
  rw [orderOf_eq_prime_iff]
  refine ⟨?_, r_zpow_mul_s_ne_one n hn _⟩
  rw [reflection_zpow_square n hn, zpow_mul, zpow_ofNat, z_sq n hn, one_zpow]

theorem odd_reflection_order (n : ℕ) (hn : 3 ≤ n) (j : ℤ) :
    orderOf (r n ^ (2 * j + 1) * s n) = 4 := by
  have hs : (r n ^ (2 * j + 1) * s n) ^ 2 = z n := by
    rw [reflection_zpow_square n hn, zpow_add, zpow_mul, zpow_ofNat,
      z_sq n hn, one_zpow, zpow_one, one_mul]
  have hsq : (r n ^ (2 * j + 1) * s n) ^ 2 ≠ 1 := by
    rw [hs]
    exact z_ne_one n hn
  have hfour : (r n ^ (2 * j + 1) * s n) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs, z_sq n hn]
  have ho := orderOf_eq_prime_pow (x := r n ^ (2 * j + 1) * s n) (n := 1) (p := 2)
    (by simpa using hsq) (by simpa using hfour)
  simpa using ho

theorem involution_iff (n : ℕ) (hn : 3 ≤ n) (g : SemidihedralGroup n) :
    orderOf g = 2 ↔ g = z n ∨
      ∃ j : Fin (half n), g = r n ^ (2 * j.val) * s n := by
  constructor
  · intro hg
    obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective g
    change orderOf (element n hn i e) = 2 at hg
    change element n hn i e = z n ∨
      ∃ j : Fin (half n), element n hn i e = r n ^ (2 * j.val) * s n
    rcases exponent_cases e with rfl | rfl
    · left
      rw [(rotation_involution_iff n hn i).mp hg, ← z_eq_element n hn]
    · right
      have heven := (outside_involution_iff n hn i).mp hg
      have hval : i.val = 2 * (i.val / 2) := by
        have hdecomp := Nat.mod_add_div i.val 2
        omega
      have hj : i.val / 2 < half n := by
        have hlt := ZMod.val_lt i
        have hm := modulus_eq_two_mul_half (by omega : 2 ≤ n)
        omega
      refine ⟨⟨i.val / 2, hj⟩, ?_⟩
      rw [element_eq]
      simp only [ZMod.val_one_eq_one_mod, show (1 % 2 : ℕ) = 1 by decide, pow_one]
      conv_lhs => rw [hval]
  · rintro (rfl | ⟨j, rfl⟩)
    · exact orderOf_z n hn
    · have h := even_reflection_order n hn (j.val : ℤ)
      change orderOf (r n ^ ((2 : ℕ) * j.val : ℤ) * s n) = 2 at h
      rw [← Int.natCast_mul, zpow_natCast] at h
      exact h

theorem quarter_residue_ne_zero (n : ℕ) (hn : 4 ≤ n) :
    ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) ≠ 0 := by
  intro h
  have hp : 0 < 2 ^ (n - 3) := pow_pos (by decide) _
  have hm : modulus n = 4 * 2 ^ (n - 3) := by
    rw [modulus_eq_two_mul_half (by omega), half_eq_two_mul_quarter (by omega)]
    ring
  have hv := congrArg (fun x : ZMod (modulus n) => x.val) h
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
  omega

theorem rotation_order_four_iff (n : ℕ) (hn : 4 ≤ n) (i : ZMod (modulus n)) :
    orderOf (element n (by omega) i 0) = 4 ↔
      i = ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) ∨
      i = -((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
  have hp : 0 < 2 ^ (n - 3) := pow_pos (by decide) _
  have hhalf : half n = 2 * 2 ^ (n - 3) := half_eq_two_mul_quarter (by omega)
  have hm : modulus n = 4 * 2 ^ (n - 3) := by
    rw [modulus_eq_two_mul_half (by omega), hhalf]
    ring
  have hnegative : -((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) =
      ((3 * 2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
    apply Eq.symm
    apply eq_neg_iff_add_eq_zero.mpr
    rw [← Nat.cast_add, show 3 * 2 ^ (n - 3) + 2 ^ (n - 3) = modulus n by omega]
    exact ZMod.natCast_self _
  constructor
  · intro ho
    have hpow := pow_orderOf_eq_one (element n (by omega) i 0)
    rw [ho, element_rotation_pow, nsmul_eq_mul, Nat.cast_ofNat,
      element_eq_one_iff] at hpow
    have hcast : 4 * i = ((4 * i.val : ℕ) : ZMod (modulus n)) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_ofNat]
    rw [hcast, ZMod.natCast_eq_zero_iff] at hpow
    have hdiv : 2 ^ (n - 3) ∣ i.val := by
      have hd : modulus n ∣ 4 * i.val := hpow.1
      have hdivide (t : ℕ) : modulus n ∣ 4 * t ↔ 2 ^ (n - 3) ∣ t := by
        rw [hm, Nat.mul_dvd_mul_iff_left (by decide : 0 < (4 : ℕ))]
      exact (hdivide i.val).mp hd
    obtain ⟨k, hk⟩ := hdiv
    have hbound : k < 4 := by
      have hlt := ZMod.val_lt i
      have hlt' : i.val < 4 * 2 ^ (n - 3) := by omega
      rw [hk] at hlt'
      nlinarith
    have hnot : i ≠ 0 ∧ i ≠ (half n : ZMod (modulus n)) := by
      have hsq : element n (by omega) i 0 ^ 2 ≠ 1 := by
        intro hs
        have hd := orderOf_dvd_of_pow_eq_one hs
        rw [ho] at hd
        omega
      rw [element_rotation_pow, nsmul_eq_mul, Nat.cast_ofNat, ne_eq,
        element_eq_one_iff, two_mul_eq_zero_iff n (by omega)] at hsq
      tauto
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exfalso
      apply hnot.1
      apply ZMod.val_injective
      simpa only [Nat.mul_zero, ZMod.val_zero] using hk
    · left
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt (by omega)]
      simpa only [Nat.mul_one] using hk
    · exfalso
      apply hnot.2
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
    · right
      rw [hnegative]
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt (by omega)]
      omega
  · intro hi
    have hs : element n (by omega) i 0 ^ 2 = z n := by
      rw [element_rotation_pow, nsmul_eq_mul, Nat.cast_ofNat, z_eq_element n (by omega)]
      apply (element_eq_iff n (by omega) _ _ _ _).mpr
      refine ⟨?_, rfl⟩
      rcases hi with rfl | rfl
      · rw [hhalf]
        push_cast
        rfl
      · have hh := two_mul_half_residue n (by omega)
        rw [hhalf] at hh ⊢
        push_cast at hh ⊢
        linear_combination -hh
    have hsq : element n (by omega) i 0 ^ 2 ≠ 1 := by
      rw [hs]
      exact z_ne_one n (by omega)
    have hfour : element n (by omega) i 0 ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs, z_sq n (by omega)]
    have ho := orderOf_eq_prime_pow (x := element n (by omega) i 0) (n := 1) (p := 2)
      (by simpa using hsq) (by simpa using hfour)
    simpa using ho

end CFSG.Semidihedral
