module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open scoped commutatorElement

section NormalForm

variable {G : Type*} [Group G]

theorem commutator_pow_eq_one_of_commute {a b : G} {p : ℕ} (hb : Commute ⁅a, b⁆ b)
    (hbp : b ^ p = 1) : ⁅a, b⁆ ^ p = 1 := by
  set w := ⁅a, b⁆ with hw
  have hab : a * b = w * (b * a) := by rw [hw, commutatorElement_def]; group
  have key : ∀ k : ℕ, a * b ^ k = w ^ k * (b ^ k * a) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a * b ^ (k + 1) = (a * b ^ k) * b := by rw [pow_succ, mul_assoc]
        _ = (w ^ k * (b ^ k * a)) * b := by rw [ih]
        _ = w ^ k * (b ^ k * (a * b)) := by simp only [mul_assoc]
        _ = w ^ k * (b ^ k * (w * (b * a))) := by rw [hab]
        _ = w ^ k * (w * (b ^ k * (b * a))) := by
            rw [← mul_assoc (b ^ k) w, ((hb.pow_right k).eq).symm, mul_assoc]
        _ = w ^ (k + 1) * (b ^ (k + 1) * a) := by
            rw [pow_succ w k, pow_succ b k]
            simp only [mul_assoc]
  have h5 := key p
  rw [hbp, mul_one, one_mul] at h5
  have : w ^ p * a = 1 * a := by rw [one_mul]; exact h5.symm
  exact mul_right_cancel this

variable {x y : G}

theorem heis_pow_comm (hzy : Commute ⁅y, x⁆ y) (hzx : Commute ⁅y, x⁆ x) (i j : ℕ) :
    y ^ j * x ^ i = ⁅y, x⁆ ^ (i * j) * (x ^ i * y ^ j) := by
  set z := ⁅y, x⁆ with hz
  have hyx : y * x * y⁻¹ = z * x := by rw [hz, commutatorElement_def]; group
  have h1 : ∀ j : ℕ, y ^ j * x * (y ^ j)⁻¹ = z ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * x * (y ^ (j + 1)) ⁻¹ = y * (y ^ j * x * (y ^ j)⁻¹) * y⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = y * (z ^ j * x) * y⁻¹ := by rw [ih]
        _ = (y * z ^ j * y⁻¹) * (y * x * y⁻¹) := by group
        _ = z ^ (j + 1) * x := by
            have : y * z ^ j * y⁻¹ = z ^ j := by
              have h := (Commute.pow_right hzy.symm j).eq
              calc y * z ^ j * y⁻¹ = z ^ j * y * y⁻¹ := by rw [h]
                _ = z ^ j := by group
            rw [hyx, pow_succ, this, mul_assoc]
  have h2 : y ^ j * x ^ i * (y ^ j)⁻¹ = z ^ (j * i) * x ^ i := by
    calc y ^ j * x ^ i * (y ^ j)⁻¹ = (y ^ j * x * (y ^ j)⁻¹) ^ i := by rw [conj_pow]
      _ = (z ^ j * x) ^ i := by rw [h1]
      _ = z ^ (j * i) * x ^ i := by
          rw [(hzx.pow_left j).mul_pow i, ← pow_mul]
  calc y ^ j * x ^ i = (y ^ j * x ^ i * (y ^ j)⁻¹) * y ^ j := by group
    _ = (z ^ (j * i) * x ^ i) * y ^ j := by rw [h2]
    _ = z ^ (i * j) * (x ^ i * y ^ j) := by rw [mul_comm j i, mul_assoc]

theorem heis_normal_form (hx5 : x ^ 5 = 1) (hy5 : y ^ 5 = 1) (hzx : Commute ⁅y, x⁆ x)
    (hzy : Commute ⁅y, x⁆ y) :
    ∀ u ∈ Subgroup.closure ({x, y} : Set G), ∃ i j k : ℕ, u = x ^ i * y ^ j * ⁅y, x⁆ ^ k := by
  set z := ⁅y, x⁆ with hz
  have hzxk : ∀ k : ℕ, z ^ k * x = x * z ^ k := fun k => (hzx.pow_left k).eq
  have hzyk : ∀ k : ℕ, z ^ k * y = y * z ^ k := fun k => (hzy.pow_left k).eq
  have hcomm : ∀ a b c m : ℕ, z ^ m * (x ^ a * y ^ b * z ^ c) = (x ^ a * y ^ b * z ^ c) * z ^ m :=
    fun a b c m =>
      ((((hzx.pow_right a).mul_right (hzy.pow_right b)).mul_right
        ((Commute.refl z).pow_right c)).pow_left m).eq
  have M1 : ∀ i j k : ℕ, (x ^ i * y ^ j * z ^ k) * x = x ^ (i + 1) * y ^ j * z ^ (k + j) := by
    intro i j k
    have hyx1 : y ^ j * x = z ^ j * (x * y ^ j) := by
      have := heis_pow_comm hzy hzx 1 j
      simpa using this
    calc (x ^ i * y ^ j * z ^ k) * x = x ^ i * y ^ j * (z ^ k * x) := by rw [mul_assoc]
      _ = x ^ i * y ^ j * (x * z ^ k) := by rw [hzxk]
      _ = x ^ i * (y ^ j * x) * z ^ k := by simp only [mul_assoc]
      _ = x ^ i * (z ^ j * (x * y ^ j)) * z ^ k := by rw [hyx1]
      _ = z ^ j * (x ^ (i + 1) * y ^ j * z ^ k) := by
          have hzi : x ^ i * z ^ j = z ^ j * x ^ i := ((hzx.pow_pow j i).eq).symm
          calc x ^ i * (z ^ j * (x * y ^ j)) * z ^ k
              = (x ^ i * z ^ j) * (x * y ^ j) * z ^ k := by simp only [mul_assoc]
            _ = z ^ j * x ^ i * (x * y ^ j) * z ^ k := by rw [hzi]
            _ = z ^ j * (x ^ (i + 1) * y ^ j * z ^ k) := by rw [pow_succ]; simp only [mul_assoc]
      _ = (x ^ (i + 1) * y ^ j * z ^ k) * z ^ j := hcomm _ _ _ _
      _ = x ^ (i + 1) * y ^ j * z ^ (k + j) := by rw [mul_assoc _ (z ^ k), ← pow_add]
  have M2 : ∀ i j k : ℕ, (x ^ i * y ^ j * z ^ k) * y = x ^ i * y ^ (j + 1) * z ^ k := by
    intro i j k
    calc (x ^ i * y ^ j * z ^ k) * y = x ^ i * y ^ j * (z ^ k * y) := by rw [mul_assoc]
      _ = x ^ i * y ^ j * (y * z ^ k) := by rw [hzyk]
      _ = x ^ i * y ^ (j + 1) * z ^ k := by rw [pow_succ]; simp only [mul_assoc]
  have hxi : x⁻¹ = x ^ 4 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx5]
  have hyi : y⁻¹ = y ^ 4 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', hy5]
  intro u hu
  refine Subgroup.closure_induction_right (p := fun g _ => ∃ i j k : ℕ,
    g = x ^ i * y ^ j * z ^ k) ⟨0, 0, 0, by simp⟩ ?_ ?_ hu
  · rintro g - h hh ⟨i, j, k, rfl⟩
    rcases hh with hhx | hhy
    · rw [hhx]
      exact ⟨i + 1, j, k + j, M1 i j k⟩
    · rw [Set.mem_singleton_iff] at hhy
      rw [hhy]
      exact ⟨i, j + 1, k, M2 i j k⟩
  · rintro g - h hh ⟨i, j, k, rfl⟩
    rcases hh with hhx | hhy
    · rw [hhx, hxi]
      have e : (x ^ i * y ^ j * z ^ k) * x ^ 4 =
          ((((x ^ i * y ^ j * z ^ k) * x) * x) * x) * x := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e, M1, M1, M1, M1]
      exact ⟨_, _, _, rfl⟩
    · rw [Set.mem_singleton_iff] at hhy
      rw [hhy, hyi]
      have e : (x ^ i * y ^ j * z ^ k) * y ^ 4 =
          ((((x ^ i * y ^ j * z ^ k) * y) * y) * y) * y := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e, M2, M2, M2, M2]
      exact ⟨_, _, _, rfl⟩

end NormalForm

end CFSG.CGT.PushingUpLit.CGT6M
