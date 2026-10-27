module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

theorem two_pow_pair_ne_aux {a l l' : ℕ} (ha : 1 ≤ a) (hl : l < l') (hl' : l' < 2 * a + 1)
    (h : (2 ^ l + 2 ^ l') % (2 ^ (2 * a + 1) - 1) = 2 ^ a % (2 ^ (2 * a + 1) - 1)) : False := by
  have hq : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by rw [pow_succ]; ring
  have hP : 4 ≤ 2 ^ (2 * a) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB : 2 ^ l' ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hE : 2 ^ a ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 2 * 2 ^ l ≤ 2 ^ l' := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hApos : 0 < 2 ^ l := Nat.two_pow_pos l
  have h1 : (2 ^ l + 2 ^ l') % (2 ^ (2 * a + 1) - 1) = 2 ^ l + 2 ^ l' :=
    Nat.mod_eq_of_lt (by omega)
  have h2 : 2 ^ a % (2 ^ (2 * a + 1) - 1) = 2 ^ a := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2] at h
  have h3 : 2 ^ l' < 2 ^ a := by omega
  have h4 : l' < a := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h3
  have h5 : 2 ^ (l' + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ] at h5
  omega

theorem two_pow_add_two_pow_modEq {a l l' : ℕ} (ha : 1 ≤ a) (hl : l < 2 * a + 1)
    (hl' : l' < 2 * a + 1)
    (h : (2 ^ l + 2 ^ l') % (2 ^ (2 * a + 1) - 1) = 2 ^ a % (2 ^ (2 * a + 1) - 1)) :
    l = a - 1 ∧ l' = a - 1 := by
  rcases lt_trichotomy l l' with hlt | heq | hgt
  · exact (two_pow_pair_ne_aux ha hlt hl' h).elim
  · subst heq
    have hq : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by rw [pow_succ]; ring
    have hP : 4 ≤ 2 ^ (2 * a) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hE : 2 ^ a ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ a % (2 ^ (2 * a + 1) - 1) = 2 ^ a := Nat.mod_eq_of_lt (by omega)
    have hsum : 2 ^ l + 2 ^ l = 2 ^ (l + 1) := by rw [pow_succ]; ring
    rw [hsum, h2] at h
    by_cases hc : l + 1 ≤ 2 * a
    · have hle : 2 ^ (l + 1) ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) hc
      rw [Nat.mod_eq_of_lt (by omega)] at h
      have := Nat.pow_right_injective (le_refl 2) h
      omega
    · have hl2 : l = 2 * a := by omega
      subst hl2
      have hq1 : 2 ^ (2 * a + 1) - 1 + 1 = 2 ^ (2 * a + 1) := Nat.sub_add_cancel Nat.one_le_two_pow
      have h8 : 1 < 2 ^ (2 * a + 1) - 1 := by omega
      have hmod : 2 ^ (2 * a + 1) % (2 ^ (2 * a + 1) - 1) = 1 :=
        calc 2 ^ (2 * a + 1) % (2 ^ (2 * a + 1) - 1)
            = (2 ^ (2 * a + 1) - 1 + 1) % (2 ^ (2 * a + 1) - 1) := by rw [hq1]
          _ = 1 % (2 ^ (2 * a + 1) - 1) := Nat.add_mod_left _ _
          _ = 1 := Nat.mod_eq_of_lt h8
      rw [hmod] at h
      have : 1 < 2 ^ a := Nat.one_lt_two_pow (by omega)
      omega
  · exact (two_pow_pair_ne_aux ha hgt hl (by rwa [add_comm])).elim

theorem exists_unit_pow_eq {K : Type*} [Field K] [Fintype K] {a : ℕ}
    (hcard : Fintype.card K = 2 ^ (2 * a + 1)) {u : K} (hu : u ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ x ^ (1 + 2 ^ (a + 1)) = u ∧ x ^ (1 + 2 ^ a) = u ^ (2 ^ a) := by
  have hqK : Fintype.card K = 2 * (2 ^ a * 2 ^ a) := by rw [hcard]; ring
  have hθ : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
  have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
  generalize 2 ^ a = ε at hqK hθ hpos ⊢
  rw [hθ]
  obtain ⟨e, rfl⟩ : ∃ e, ε = e + 1 := ⟨ε - 1, by omega⟩
  refine ⟨u ^ (2 * e + 1), pow_ne_zero _ hu, ?_, ?_⟩
  · have h2 : u ^ ((2 * e + 1) * (1 + 2 * (e + 1))) * u = u * u := by
      calc _ = u ^ ((2 * e + 1) * (1 + 2 * (e + 1)) + 1) := (pow_succ _ _).symm
        _ = u ^ (2 * Fintype.card K) := by congr 1; rw [hqK]; ring
        _ = (u ^ Fintype.card K) ^ 2 := pow_mul' _ _ _
        _ = u * u := by rw [FiniteField.pow_card]; ring
    rw [← pow_mul]
    exact mul_right_cancel₀ hu h2
  · have h3 : u ^ ((2 * e + 1) * (1 + (e + 1))) * u = u ^ (e + 1) * u := by
      calc _ = u ^ ((2 * e + 1) * (1 + (e + 1)) + 1) := (pow_succ _ _).symm
        _ = u ^ ((e + 1) + Fintype.card K) := by congr 1; rw [hqK]; ring
        _ = u ^ (e + 1) * u := by rw [pow_add, FiniteField.pow_card]
    rw [← pow_mul]
    exact mul_right_cancel₀ hu h3

end CFSG.CGT.PushingUpLit.SolKNA
