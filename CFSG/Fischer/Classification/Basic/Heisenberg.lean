module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Fischer.Classification

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem sq_eq_inv_of_pow_three {u : G} (hu : u ^ 3 = 1) : u ^ 2 = u⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hu])

theorem mul_eq_one_of_inv_mul_inv_eq {u v : G} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (h : u⁻¹ * v⁻¹ = u * v) : u * v = 1 := by
  have hu2 : u * u = u⁻¹ := by rw [← sq]; exact sq_eq_inv_of_pow_three hu
  have hv2 : v⁻¹ * v⁻¹ = v := by rw [← mul_inv_rev, ← sq, sq_eq_inv_of_pow_three hv, inv_inv]
  have h1 : v⁻¹ = u * u * v := by
    calc v⁻¹ = u * (u⁻¹ * v⁻¹) := by group
      _ = u * (u * v) := by rw [h]
      _ = u * u * v := by group
  have h2 : v = u⁻¹ := by
    calc v = v⁻¹ * v⁻¹ := hv2.symm
      _ = u * u * v * v⁻¹ := by rw [← h1]
      _ = u * u := by group
      _ = u⁻¹ := hu2
  rw [h2, mul_inv_cancel]

theorem commute_conj_of_cube {a b : G} (hb : b ^ 3 = 1) (h1 : (a * b) ^ 3 = 1)
    (h2 : (a * b⁻¹) ^ 3 = 1) : Commute a (b⁻¹ * a * b) := by
  have hbb : b * b = b⁻¹ := by rw [← sq]; exact sq_eq_inv_of_pow_three hb
  have hbb' : b⁻¹ * b⁻¹ = b := by rw [← mul_inv_rev, hbb, inv_inv]
  have e1 : a * b * a = b⁻¹ * a⁻¹ * b⁻¹ := by
    have h : a * b * a * (b * a * b) = 1 := by rw [← h1, pow_three']; group
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h]
    group
  have e2 : a * b⁻¹ * a = b * a⁻¹ * b := by
    have h : a * b⁻¹ * a * (b⁻¹ * a * b⁻¹) = 1 := by rw [← h2, pow_three']; group
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h]
    group
  show a * (b⁻¹ * a * b) = b⁻¹ * a * b * a
  calc a * (b⁻¹ * a * b) = a * b⁻¹ * a * b := by group
    _ = b * a⁻¹ * (b * b) := by rw [e2]; group
    _ = b⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ := by rw [hbb, hbb']
    _ = b⁻¹ * (a * b * a) := by rw [e1]; group
    _ = b⁻¹ * a * b * a := by group

structure CubeRel (x y : G) : Prop where
  cube_left : x ^ 3 = 1
  cube_right : y ^ 3 = 1
  cube_mul : (x * y) ^ 3 = 1
  cube_mul_inv : (x * y⁻¹) ^ 3 = 1

namespace CubeRel

variable {x y : G} (h : CubeRel x y)
include h

theorem cube_mul_rev : (y * x) ^ 3 = 1 := by
  have : (y * x) ^ 3 = y * (x * y) ^ 3 * y⁻¹ := by
    rw [← conj_pow, show y * (x * y) * y⁻¹ = y * x by group]
  rw [this, h.cube_mul, mul_one, mul_inv_cancel]

theorem cube_inv_mul : (x⁻¹ * y) ^ 3 = 1 := by
  rw [show x⁻¹ * y = x⁻¹ * (x * y⁻¹)⁻¹ * x⁻¹⁻¹ by group, conj_pow, inv_pow, h.cube_mul_inv,
    inv_one, mul_one, mul_inv_cancel]

theorem cube_inv_mul_inv : (x⁻¹ * y⁻¹) ^ 3 = 1 := by
  rw [← mul_inv_rev, inv_pow, h.cube_mul_rev, inv_one]

theorem cube_mul_inv_rev : (y * x⁻¹) ^ 3 = 1 := by
  rw [show y * x⁻¹ = (x * y⁻¹)⁻¹ by group, inv_pow, h.cube_mul_inv, inv_one]

theorem commute_commutator_left : Commute ⁅x, y⁆ x := by
  have hc : Commute x (y * x * y⁻¹) := by
    have := commute_conj_of_cube (a := x) (b := y⁻¹) (by rw [inv_pow, h.cube_right, inv_one])
      h.cube_mul_inv (by rw [inv_inv]; exact h.cube_mul)
    rwa [inv_inv] at this
  rw [show ⁅x, y⁆ = x * (y * x * y⁻¹)⁻¹ by rw [commutatorElement_def]; group]
  exact ((Commute.refl x).mul_right hc.inv_right).symm

theorem commute_commutator_right : Commute ⁅x, y⁆ y := by
  have hc : Commute y (x * y * x⁻¹) := by
    have := commute_conj_of_cube (a := y) (b := x⁻¹) (by rw [inv_pow, h.cube_left, inv_one])
      h.cube_mul_inv_rev (by rw [inv_inv]; exact h.cube_mul_rev)
    rwa [inv_inv] at this
  rw [commutatorElement_def]
  exact hc.symm.mul_left (Commute.refl y).inv_left

theorem mul_comm_eq : y * x = x * y * ⁅x, y⁆⁻¹ := by
  have hc : Commute ⁅x, y⁆ (x * y) := h.commute_commutator_left.mul_right h.commute_commutator_right
  have h1 : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  calc y * x = ⁅x, y⁆⁻¹ * (x * y) := by rw [h1]; group
    _ = x * y * ⁅x, y⁆⁻¹ := hc.inv_left.eq

theorem mul_pow_eq (i : ℕ) : y * x ^ i = x ^ i * y * (⁅x, y⁆⁻¹) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hc : Commute ((⁅x, y⁆⁻¹) ^ i) x := (h.commute_commutator_left.inv_left).pow_left i
    calc y * x ^ (i + 1) = y * x ^ i * x := by rw [pow_succ, mul_assoc]
      _ = x ^ i * y * ((⁅x, y⁆⁻¹) ^ i * x) := by rw [ih]; simp only [mul_assoc]
      _ = x ^ i * (y * x) * (⁅x, y⁆⁻¹) ^ i := by rw [hc.eq]; simp only [mul_assoc]
      _ = x ^ (i + 1) * y * (⁅x, y⁆⁻¹) ^ (i + 1) := by
        rw [h.mul_comm_eq, pow_succ, pow_succ']; simp only [mul_assoc]

theorem commutator_pow_three : ⁅x, y⁆ ^ 3 = 1 := by
  have h3 := h.mul_pow_eq 3
  rw [h.cube_left, one_mul, mul_one, left_eq_mul, inv_pow, inv_eq_one] at h3
  exact h3

theorem commutator_inv_inv : ⁅x⁻¹, y⁻¹⁆ = ⁅x, y⁆ := by
  have hc : Commute ⁅x, y⁆ (x⁻¹ * y⁻¹) :=
    h.commute_commutator_left.inv_right.mul_right h.commute_commutator_right.inv_right
  have h1 : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  calc ⁅x⁻¹, y⁻¹⁆ = x⁻¹ * y⁻¹ * (x * y) := by rw [commutatorElement_def]; group
    _ = x⁻¹ * y⁻¹ * ⁅x, y⁆ * (y * x) := by rw [h1]; group
    _ = ⁅x, y⁆ * (x⁻¹ * y⁻¹ * (y * x)) := by rw [← hc.eq]; group
    _ = ⁅x, y⁆ := by group

theorem exists_eq_of_mem_closure {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ i j k : ℕ, i < 3 ∧ j < 3 ∧ k < 3 ∧ g = x ^ i * y ^ j * ⁅x, y⁆ ^ k := by
  have hc3 : ⁅x, y⁆ ^ 3 = 1 := h.commutator_pow_three
  let P : G → Prop := fun g => ∃ i j k : ℕ, g = x ^ i * y ^ j * ⁅x, y⁆ ^ k
  have hxP : ∀ g, P g → P (x * g) := by
    rintro g ⟨i, j, k, rfl⟩
    exact ⟨i + 1, j, k, by rw [pow_succ']; simp only [mul_assoc]⟩
  have hyP : ∀ g, P g → P (y * g) := by
    rintro g ⟨i, j, k, rfl⟩
    refine ⟨i, j + 1, 2 * i + k, ?_⟩
    have hcy : Commute ((⁅x, y⁆⁻¹) ^ i) (y ^ j) :=
      ((h.commute_commutator_right.inv_left).pow_left i).pow_right j
    have hci : ⁅x, y⁆ ^ (2 * i + k) = (⁅x, y⁆⁻¹) ^ i * ⁅x, y⁆ ^ k := by
      rw [pow_add, pow_mul, sq_eq_inv_of_pow_three hc3]
    rw [hci]
    calc y * (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = y * x ^ i * y ^ j * ⁅x, y⁆ ^ k := by
          simp only [mul_assoc]
      _ = x ^ i * y * ((⁅x, y⁆⁻¹) ^ i * y ^ j) * ⁅x, y⁆ ^ k := by
          rw [h.mul_pow_eq]; simp only [mul_assoc]
      _ = x ^ i * y * (y ^ j * (⁅x, y⁆⁻¹) ^ i) * ⁅x, y⁆ ^ k := by rw [hcy.eq]
      _ = x ^ i * y ^ (j + 1) * ((⁅x, y⁆⁻¹) ^ i * ⁅x, y⁆ ^ k) := by
          rw [pow_succ']; simp only [mul_assoc]
  have hxinv : x⁻¹ = x ^ 2 := (sq_eq_inv_of_pow_three h.cube_left).symm
  have hyinv : y⁻¹ = y ^ 2 := (sq_eq_inv_of_pow_three h.cube_right).symm
  have hpowP : ∀ s : G, (∀ g, P g → P (s * g)) → ∀ n g, P g → P (s ^ n * g) := by
    intro s hs n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ n ih => intro g hg; rw [pow_succ', mul_assoc]; exact hs _ (ih g hg)
  have hP : P g := by
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul_left s hs g _ ih =>
      rcases hs with rfl | rfl
      · exact hxP _ ih
      · exact hyP _ ih
    | inv_mul_cancel s hs g _ ih =>
      rcases hs with rfl | rfl
      · rw [hxinv]; exact hpowP _ hxP _ _ ih
      · rw [hyinv]; exact hpowP _ hyP _ _ ih
  obtain ⟨i, j, k, rfl⟩ := hP
  exact ⟨i % 3, j % 3, k % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), by
      rw [← pow_eq_pow_mod _ h.cube_left, ← pow_eq_pow_mod _ h.cube_right,
        ← pow_eq_pow_mod _ hc3]⟩

theorem pow_three_eq_one {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) : g ^ 3 = 1 := by
  obtain ⟨i, j, k, hi, hj, -, rfl⟩ := h.exists_eq_of_mem_closure hg
  have hc : Commute (x ^ i * y ^ j) (⁅x, y⁆ ^ k) :=
    ((h.commute_commutator_left.pow_pow k i).symm).mul_left
      ((h.commute_commutator_right.pow_pow k j).symm)
  rw [hc.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, h.commutator_pow_three, one_pow, mul_one]
  have hx2 := sq_eq_inv_of_pow_three h.cube_left
  have hy2 := sq_eq_inv_of_pow_three h.cube_right
  interval_cases i <;> interval_cases j <;>
    simp only [pow_zero, pow_one, hx2, hy2, one_mul, mul_one, one_pow, inv_pow, h.cube_left,
      h.cube_right, inv_one, h.cube_mul, h.cube_mul_inv, h.cube_inv_mul, h.cube_inv_mul_inv]

end CubeRel

end CFSG.Fischer.Classification
