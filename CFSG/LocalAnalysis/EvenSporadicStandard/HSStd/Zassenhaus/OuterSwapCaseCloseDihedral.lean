module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup

variable {G : Type} [Group G]

@[expose] def dihF (t a : G) : DihedralGroup 4 → G
  | .r i => a ^ i.val
  | .sr i => t * a ^ i.val

theorem pow_eq_pow_of_natCast_eq {a : G} (ha4 : a ^ 4 = 1) {x y : ℕ}
    (h : (x : ZMod 4) = (y : ZMod 4)) : a ^ x = a ^ y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [pow_eq_pow_mod x ha4, pow_eq_pow_mod y ha4, h]

theorem exists_dihedral_hom (t a : G) (ht : t * t = 1) (ha2 : a * a ≠ 1) (ha4 : a ^ 4 = 1)
    (hta : t * a * t = a⁻¹) :
    ∃ f : DihedralGroup 4 →* G, Function.Injective f ∧
      ∀ N : Subgroup G, t ∈ N → a ∈ N → ∀ x, f x ∈ N := by
  have hpow : ∀ {x y : ℕ}, (x : ZMod 4) = (y : ZMod 4) → a ^ x = a ^ y :=
    fun h => pow_eq_pow_of_natCast_eq ha4 h
  have h4 : (4 : ZMod 4) = 0 := by decide
  have ha3 : a ^ 3 = a⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc a ^ 3 * a = a ^ 4 := by rw [← pow_succ]
      _ = 1 := ha4
  have hat : a * t = t * a ^ 3 := by
    rw [ha3, ← hta]
    calc a * t = (t * t) * a * t := by rw [ht, one_mul]
      _ = t * (t * a * t) := by group
  have hcomm : ∀ n : ℕ, a ^ n * t = t * a ^ (3 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * t = a ^ n * (a * t) := by rw [pow_succ, mul_assoc]
        _ = a ^ n * (t * a ^ 3) := by rw [hat]
        _ = (a ^ n * t) * a ^ 3 := by rw [mul_assoc]
        _ = t * a ^ (3 * n) * a ^ 3 := by rw [ih]
        _ = t * a ^ (3 * (n + 1)) := by rw [mul_assoc, ← pow_add, mul_add, mul_one]
  have hmul : ∀ x y : DihedralGroup 4, dihF t a (x * y) = dihF t a x * dihF t a y := by
    intro x y
    cases x with
    | r i =>
      cases y with
      | r j =>
        simp only [DihedralGroup.r_mul_r, dihF]
        rw [← pow_add]
        apply hpow
        push_cast
        simp
      | sr j =>
        simp only [DihedralGroup.r_mul_sr, dihF]
        rw [← mul_assoc, hcomm, mul_assoc, ← pow_add]
        congr 1
        apply hpow
        push_cast
        simp only [ZMod.natCast_zmod_val]
        linear_combination (-i) * h4
    | sr i =>
      cases y with
      | r j =>
        simp only [DihedralGroup.sr_mul_r, dihF]
        rw [mul_assoc, ← pow_add]
        congr 1
        apply hpow
        push_cast
        simp
      | sr j =>
        simp only [DihedralGroup.sr_mul_sr, dihF]
        calc a ^ (j - i).val = (t * t) * a ^ (j - i).val := by rw [ht, one_mul]
          _ = t * (t * a ^ (3 * i.val + j.val)) := by
            rw [mul_assoc]
            congr 2
            apply hpow
            push_cast
            simp only [ZMod.natCast_zmod_val]
            linear_combination (-i) * h4
          _ = t * (t * a ^ (3 * i.val)) * a ^ j.val := by
            rw [pow_add]
            simp only [mul_assoc]
          _ = t * (a ^ i.val * t) * a ^ j.val := by rw [hcomm]
          _ = t * a ^ i.val * (t * a ^ j.val) := by simp only [mul_assoc]
  have hone : dihF t a 1 = 1 := by
    rw [DihedralGroup.one_def]
    simp [dihF]
  have hord : orderOf a = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a)
      (by simpa [pow_two] using ha2) (by simpa using ha4)
    simpa using this
  have hat' : a * t = t * a → False := by
    intro hc
    rw [hat] at hc
    have h1 : a = a ^ 3 := mul_left_cancel hc.symm
    apply ha2
    have h2 : a * 1 = a * (a * a) := by
      rw [mul_one]
      calc a = a ^ 3 := h1
        _ = a * (a * a) := by simp [pow_succ, mul_assoc]
    exact (mul_left_cancel h2).symm
  refine ⟨⟨⟨dihF t a, hone⟩, hmul⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    change dihF t a x = 1 at hx
    cases x with
    | r i =>
      simp only [dihF] at hx
      have hd : 4 ∣ i.val := by
        have := orderOf_dvd_of_pow_eq_one hx
        rwa [hord] at this
      have : i = 0 := by
        rw [← ZMod.natCast_zmod_val i]
        exact (ZMod.natCast_eq_zero_iff _ _).2 hd
      rw [this, DihedralGroup.one_def]
    | sr i =>
      exfalso
      simp only [dihF] at hx
      have h1 : a ^ i.val = t := by
        calc a ^ i.val = (t * t) * a ^ i.val := by rw [ht, one_mul]
          _ = t * (t * a ^ i.val) := by rw [mul_assoc]
          _ = t := by rw [hx, mul_one]
      apply hat'
      rw [← h1, ← pow_succ', pow_succ]
  · intro N htN haN x
    cases x with
    | r i => exact pow_mem haN _
    | sr i => exact mul_mem htN (pow_mem haN _)

theorem exists_dihedral_subgroup (t a : G) (ht : t * t = 1) (ha2 : a * a ≠ 1) (ha4 : a ^ 4 = 1)
    (hta : t * a * t = a⁻¹) :
    ∃ Q : Subgroup G, Nat.card Q = 8 ∧ IsPGroup 2 Q ∧
      ∀ N : Subgroup G, t ∈ N → a ∈ N → Q ≤ N := by
  obtain ⟨f, hf, hN⟩ := exists_dihedral_hom t a ht ha2 ha4 hta
  have hcard : Nat.card f.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, DihedralGroup.nat_card]
  refine ⟨f.range, hcard, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  · intro N htN haN
    rintro _ ⟨x, rfl⟩
    exact hN N htN haN x

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
