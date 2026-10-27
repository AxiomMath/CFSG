module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbedding.ThompsonGen

open scoped commutatorElement

private theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

theorem pow_mul_eq_of_mul_comm {G : Type*} [Group G] {x y c : G} (hyx : y * x = x * y * c)
    (hcy : Commute c y) (n : ℕ) : y ^ n * x = x * y ^ n * c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcyn : Commute c (y ^ n) := hcy.pow_right n
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (x * y ^ n * c ^ n) := by rw [ih]
      _ = (y * x) * y ^ n * c ^ n := by simp only [mul_assoc]
      _ = x * y * c * y ^ n * c ^ n := by rw [hyx]
      _ = x * y * (c * y ^ n) * c ^ n := by simp only [mul_assoc]
      _ = x * y * (y ^ n * c) * c ^ n := by rw [hcyn.eq]
      _ = x * y ^ (n + 1) * c ^ (n + 1) := by
        rw [pow_succ' y n, pow_succ' c n]
        simp only [mul_assoc]

theorem mul_pow_eq_of_mul_comm {G : Type*} [Group G] {x y c : G} (hyx : y * x = x * y * c)
    (hcx : Commute c x) (hcy : Commute c y) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * c ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := pow_mul_eq_of_mul_comm hyx hcy n
    have hcx' : Commute (c ^ n.choose 2) x := hcx.pow_left _
    have hcy' : Commute (c ^ n.choose 2) y := hcy.pow_left _
    have hcyn : Commute (c ^ n) y := hcy.pow_left _
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * c ^ n.choose 2 * (x * y) := by rw [ih]
      _ = x ^ n * y ^ n * (c ^ n.choose 2 * x) * y := by simp only [mul_assoc]
      _ = x ^ n * y ^ n * (x * c ^ n.choose 2) * y := by rw [hcx'.eq]
      _ = x ^ n * (y ^ n * x) * c ^ n.choose 2 * y := by simp only [mul_assoc]
      _ = x ^ n * (x * y ^ n * c ^ n) * c ^ n.choose 2 * y := by rw [h1]
      _ = x ^ n * x * y ^ n * (c ^ n * (c ^ n.choose 2 * y)) := by simp only [mul_assoc]
      _ = x ^ n * x * y ^ n * (c ^ n * (y * c ^ n.choose 2)) := by rw [hcy'.eq]
      _ = x ^ n * x * y ^ n * ((c ^ n * y) * c ^ n.choose 2) := by simp only [mul_assoc]
      _ = x ^ n * x * y ^ n * ((y * c ^ n) * c ^ n.choose 2) := by rw [hcyn.eq]
      _ = x ^ n * x * (y ^ n * y) * (c ^ n * c ^ n.choose 2) := by simp only [mul_assoc]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + 1).choose 2 := by
        rw [choose_two_succ, pow_succ x n, pow_succ y n, pow_add c n]

theorem mul_pow_prime_of_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type*} [Group G]
    {x y : G} (hcx : Commute ⁅y, x⁆ x) (hcy : Commute ⁅y, x⁆ y) (hc : ⁅y, x⁆ ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have hyx : y * x = x * y * ⁅y, x⁆ :=
    calc y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
      _ = x * ⁅y, x⁆ * y := by rw [hcx.eq]
      _ = x * y * ⁅y, x⁆ := by rw [mul_assoc, hcy.eq, ← mul_assoc]
  rw [mul_pow_eq_of_mul_comm hyx hcx hcy p]
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  obtain ⟨m, hm⟩ := hp.dvd_choose_self (by norm_num : 2 ≠ 0) hp3
  rw [hm, pow_mul, hc, one_pow, mul_one]

end CFSG.AGLEmbedding.ThompsonGen
