module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ComponentClassification.AutL2Facts

open DihedralGroup Subgroup

variable {n : ℕ}

theorem card_center_dihedral (hn : 4 ≤ n) (heven : Even n) :
    Nat.card (center (DihedralGroup n)) = 2 := by
  have : NeZero n := ⟨by omega⟩
  rw [DihedralGroup.center_eq_closure_of_even_ne_two heven (by omega), Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [DihedralGroup.r_pow, DihedralGroup.one_def]
    congr 1
    obtain ⟨m, rfl⟩ := heven
    rw [show (m + m) / 2 = m by omega, ← Nat.cast_mul, show m * 2 = m + m by ring,
      ZMod.natCast_self]
  · rw [DihedralGroup.one_def, ne_eq, DihedralGroup.r.injEq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega

theorem r_half_mem_center (heven : Even n) :
    r ((n / 2 : ℕ) : ZMod n) ∈ center (DihedralGroup n) := by
  rw [mem_center_iff]
  obtain ⟨m, rfl⟩ := heven
  have hmm : ((m + m) / 2 : ℕ) = m := by omega
  have hc : (m : ZMod (m + m)) + m = 0 := by rw [← Nat.cast_add, ZMod.natCast_self]
  rw [hmm]
  rintro (i | i)
  · simp only [r_mul_r, add_comm]
  · simp only [r_mul_sr, sr_mul_r, sr.injEq]
    linear_combination hc

theorem dihedral_exists_sq_central {m : ℕ} (hm : 2 ≤ m) :
    ∃ t : DihedralGroup (2 ^ m), t * t ≠ 1 ∧ t * t ∈ center (DihedralGroup (2 ^ m)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hhalf : (2 ^ (m + 2) / 2 : ℕ) = 2 ^ m + 2 ^ m := by
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), pow_succ]
    ring
  refine ⟨r ((2 ^ m : ℕ) : ZMod (2 ^ (m + 2))), ?_, ?_⟩
  · rw [r_mul_r, one_def, ne_eq, r.injEq, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by positivity) h
    have h4 : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
    have : 0 < 2 ^ m := by positivity
    omega
  · have h1 := r_half_mem_center (n := 2 ^ (m + 2)) (by
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩)
    rw [hhalf, Nat.cast_add] at h1
    rwa [r_mul_r]

theorem dihedral_eq_mul_involutions (x : DihedralGroup n) :
    ∃ i j : DihedralGroup n, i * i = 1 ∧ j * j = 1 ∧ x = i * j := by
  rcases x with k | k
  · exact ⟨sr 0, sr k, sr_mul_self 0, sr_mul_self k, by rw [sr_mul_sr, sub_zero]⟩
  · exact ⟨sr k, 1, sr_mul_self k, mul_one 1, (mul_one _).symm⟩

theorem dihedral_exists_commuting_involution (heven : Even n) (hn : 2 ≤ n)
    (x : DihedralGroup n) (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ y : DihedralGroup n, y * y = 1 ∧ y ≠ 1 ∧ y ≠ x ∧ y * x = x * y := by
  have : NeZero n := ⟨by omega⟩
  have hz : r ((n / 2 : ℕ) : ZMod n) ∈ center (DihedralGroup n) := r_half_mem_center heven
  have hz1 : r ((n / 2 : ℕ) : ZMod n) ≠ 1 := by
    rw [one_def, ne_eq, r.injEq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hzz : r ((n / 2 : ℕ) : ZMod n) * r ((n / 2 : ℕ) : ZMod n) = 1 := by
    rw [r_mul_r, ← Nat.cast_add, one_def]
    obtain ⟨m, rfl⟩ := heven
    rw [show (m + m) / 2 = m by omega, ZMod.natCast_self]
  rcases x with k | k
  · refine ⟨sr 0, sr_mul_self 0, by rintro ⟨⟩, by rintro ⟨⟩, ?_⟩
    simp only [r_mul_sr, sr_mul_r, zero_add, zero_sub, sr.injEq]
    simp only [r_mul_r, one_def, r.injEq] at hx
    linear_combination hx
  · refine ⟨r ((n / 2 : ℕ) : ZMod n), hzz, hz1, by rintro ⟨⟩, ?_⟩
    exact (mem_center_iff.mp hz (sr k)).symm

theorem dihedral_card_le_two_of_commute [NeZero n] (a b : DihedralGroup n) (hab : a * b ≠ b * a)
    (C : Subgroup (DihedralGroup n)) (hC : ∀ x ∈ C, x * a = a * x ∧ x * b = b * x) :
    Nat.card C ≤ 2 := by
  classical
  have key : ∀ x ∈ C, ∃ i : ZMod n, x = r i ∧ i + i = 0 := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hC x hx
    rcases x with i | i <;> rcases a with j | j <;> rcases b with k | k <;>
      simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, r.injEq, sr.injEq, ne_eq] at hab hxa hxb
    · exact absurd (add_comm j k) hab
    · exact ⟨i, rfl, by linear_combination -hxb⟩
    · exact ⟨i, rfl, by linear_combination -hxa⟩
    · exact ⟨i, rfl, by linear_combination -hxa⟩
    · exact absurd (add_comm j k) hab
    · exact absurd (by linear_combination -hxa) hab
    · exact absurd (by linear_combination hxb) hab
    · exact absurd (by linear_combination hxb - hxa) hab
  let f : C → {i : ZMod n // 2 • i = 0} := fun x =>
    ⟨(key x.1 x.2).choose, by rw [two_nsmul]; exact (key x.1 x.2).choose_spec.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rw [(key x.1 x.2).choose_spec.1, (key y.1 y.2).choose_spec.1]
    exact congrArg r (congrArg Subtype.val hxy)
  calc Nat.card C ≤ Nat.card {i : ZMod n // 2 • i = 0} := Nat.card_le_card_of_injective f hf
    _ = (Finset.univ.filter fun i : ZMod n => 2 • i = 0).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 2 := IsAddCyclic.card_nsmul_eq_zero_le two_pos

end CFSG.ComponentClassification.AutL2Facts
