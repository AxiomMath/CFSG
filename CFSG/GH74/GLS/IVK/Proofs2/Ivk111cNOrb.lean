module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNDig

public section

namespace CFSG.GH74.GLS.Stage4.Rest

namespace Mix11cN

variable {p : ℕ}

section Two

theorem two_mul_pow_lt (hp : 3 ≤ p) {j m : ℕ} (hjm : j < m) : 2 * p ^ j < p ^ m :=
  calc 2 * p ^ j < p * p ^ j := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = p ^ (j + 1) := by ring
    _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) hjm

theorem rot_two (hp : 3 ≤ p) {m j : ℕ} (hj : j ≤ m) :
    rot p (m + 1) (2 * p ^ j) = 2 * p ^ ((j + 1) % (m + 1)) := by
  rw [rot_succ_eq]
  rcases Nat.lt_or_ge j m with hjm | hjm
  · have hlt := two_mul_pow_lt hp hjm
    rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, add_zero, Nat.mod_eq_of_lt (by omega)]
    ring
  · have hjm' : j = m := le_antisymm hj hjm
    subst hjm'
    have hpos : 0 < p ^ j := by positivity
    rw [Nat.mul_mod_left, Nat.mul_div_cancel _ hpos, Nat.mod_self]
    simp

theorem iterate_rot_two (hp : 3 ≤ p) {m j : ℕ} (hj : j ≤ m) (s : ℕ) :
    (rot p (m + 1))^[s] (2 * p ^ j) = 2 * p ^ ((j + s) % (m + 1)) := by
  induction s with
  | zero => simp [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hj)]
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih, rot_two hp (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos m)))]
    congr 2
    rw [Nat.mod_add_mod, add_assoc]

theorem orbit_two (hp : 3 ≤ p) {n : ℕ} {j j' : ℕ} (hj : j < n) (hj' : j' < n) :
    ∃ s : ℕ, 2 * p ^ j' = (rot p n)^[s] (2 * p ^ j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨j' + (m + 1) - j, ?_⟩
  rw [iterate_rot_two hp (by omega)]
  have h : j + (j' + (m + 1) - j) = j' + (m + 1) := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hj']

end Two

section Three

theorem three_lt (hp : 3 ≤ p) {k j : ℕ} (hjk : j < k) :
    (1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ j < p ^ (3 * k + 2) := by
  have hpos : 0 < p := by omega
  have e1 : p ^ j < p ^ (2 * k + 2 + j) := Nat.pow_lt_pow_right (by omega) (by omega)
  have e2 : p ^ (k + 1 + j) ≤ p ^ (2 * k + 2 + j) := Nat.pow_le_pow_right hpos (by omega)
  have e3 : p ^ (2 * k + 2 + j + 1) ≤ p ^ (3 * k + 2) := Nat.pow_le_pow_right hpos (by omega)
  have e4 : (1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ j =
      p ^ j + p ^ (k + 1 + j) + p ^ (2 * k + 2 + j) := by ring
  have e5 : p ^ (2 * k + 2 + j + 1) = p * p ^ (2 * k + 2 + j) := by ring
  have e6 : 3 * p ^ (2 * k + 2 + j) ≤ p * p ^ (2 * k + 2 + j) :=
    Nat.mul_le_mul_right _ hp
  rw [e4]
  omega

theorem rot_three_lt (hp : 3 ≤ p) {k j : ℕ} (hjk : j < k) :
    rot p (3 * (k + 1)) ((1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ j) =
      (1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ ((j + 1) % (k + 1)) := by
  have h3 : 3 * (k + 1) = (3 * k + 2) + 1 := by ring
  rw [h3, rot_succ_eq]
  have hlt := three_lt hp hjk
  rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, add_zero,
    Nat.mod_eq_of_lt (by omega : j + 1 < k + 1)]
  ring

theorem rot_three_last (hp : 3 ≤ p) (k : ℕ) :
    rot p (3 * (k + 1)) ((1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ k) =
      (1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ ((k + 1) % (k + 1)) := by
  have h3 : 3 * (k + 1) = (3 * k + 2) + 1 := by ring
  rw [h3, rot_succ_eq, Nat.mod_self, pow_zero, mul_one]
  have hpos : 0 < p := by omega
  have hlow : p ^ k + p ^ (2 * k + 1) < p ^ (3 * k + 2) := by
    have e1 : p ^ k ≤ p ^ (2 * k + 1) := Nat.pow_le_pow_right hpos (by omega)
    have e2 : p ^ (2 * k + 2) ≤ p ^ (3 * k + 2) := Nat.pow_le_pow_right hpos (by omega)
    have e3 : p ^ (2 * k + 2) = p * p ^ (2 * k + 1) := by ring
    have e4 : 3 * p ^ (2 * k + 1) ≤ p * p ^ (2 * k + 1) := Nat.mul_le_mul_right _ hp
    have e5 : 0 < p ^ (2 * k + 1) := by positivity
    omega
  have hA : (1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ k =
      (p ^ k + p ^ (2 * k + 1)) + 1 * p ^ (3 * k + 2) := by ring
  rw [hA, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlow,
    Nat.add_mul_div_right _ _ (by positivity : 0 < p ^ (3 * k + 2)), Nat.div_eq_of_lt hlow]
  ring

theorem rot_three (hp : 3 ≤ p) {k j : ℕ} (hjk : j ≤ k) :
    rot p (3 * (k + 1)) ((1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ j) =
      (1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ ((j + 1) % (k + 1)) := by
  rcases Nat.lt_or_ge j k with h | h
  · exact rot_three_lt hp h
  · have : j = k := le_antisymm hjk h
    subst this
    exact rot_three_last hp j

theorem iterate_rot_three (hp : 3 ≤ p) {k j : ℕ} (hj : j ≤ k) (s : ℕ) :
    (rot p (3 * (k + 1)))^[s] ((1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ j) =
      (1 + p ^ (k + 1) + p ^ (2 * (k + 1))) * p ^ ((j + s) % (k + 1)) := by
  induction s with
  | zero => simp [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hj)]
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih,
      rot_three hp (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos k)))]
    congr 2
    rw [Nat.mod_add_mod, add_assoc]

theorem orbit_three (hp : 3 ≤ p) {n : ℕ} (h3 : 3 ∣ n) {j j' : ℕ} (hj : j < n / 3) (hj' : j' < n / 3) :
    ∃ s : ℕ, (1 + p ^ (n / 3) + p ^ (2 * (n / 3))) * p ^ j' =
      (rot p n)^[s] ((1 + p ^ (n / 3) + p ^ (2 * (n / 3))) * p ^ j) := by
  obtain ⟨q, rfl⟩ := h3
  have hq : 3 * q / 3 = q := Nat.mul_div_cancel_left q (by norm_num)
  rw [hq] at hj hj' ⊢
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  refine ⟨j' + (k + 1) - j, ?_⟩
  rw [iterate_rot_three hp (by omega)]
  have h : j + (j' + (k + 1) - j) = j' + (k + 1) := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hj']

end Three

end Mix11cN

end CFSG.GH74.GLS.Stage4.Rest
