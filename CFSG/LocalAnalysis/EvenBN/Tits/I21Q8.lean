module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Group
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup

section Q8

variable {K : Type*} [Group K] {z p q : K}

structure Q8Rel (z p q : K) : Prop where
  z_sq : z ^ 2 = 1
  z_ne_one : z ≠ 1
  zp : z * p = p * z
  zq : z * q = q * z
  p_sq : p ^ 2 = z
  q_sq : q ^ 2 = z
  qp : q * p = z * (p * q)

namespace Q8Rel

variable (h : Q8Rel z p q)

include h

theorem z_comm_p_pow (m : ℕ) : z * p ^ m = p ^ m * z :=
  (Commute.pow_right (show Commute z p from h.zp) m).eq

theorem q_mul_p_pow (m : ℕ) : q * p ^ m = z ^ m * (p ^ m * q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc q * p ^ (m + 1) = (q * p) * p ^ m := by rw [pow_succ', mul_assoc]
      _ = z * (p * q) * p ^ m := by rw [h.qp]
      _ = z * p * (q * p ^ m) := by group
      _ = z * p * (z ^ m * (p ^ m * q)) := by rw [ih]
      _ = z ^ (m + 1) * (p ^ (m + 1) * q) := by
        have hz : p * z ^ m = z ^ m * p :=
          (Commute.pow_right (show Commute p z from h.zp.symm) m).eq
        calc z * p * (z ^ m * (p ^ m * q)) = z * (p * z ^ m) * (p ^ m * q) := by group
          _ = z * (z ^ m * p) * (p ^ m * q) := by rw [hz]
          _ = z ^ (m + 1) * (p ^ (m + 1) * q) := by rw [pow_succ', pow_succ']; group

theorem q_pow_mul_p_pow (k m : ℕ) : q ^ k * p ^ m = z ^ (k * m) * (p ^ m * q ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hz : ∀ n : ℕ, p ^ n * z = z * p ^ n := fun n => (h.z_comm_p_pow n).symm
    calc q ^ (k + 1) * p ^ m = q ^ k * (q * p ^ m) := by rw [pow_succ, mul_assoc]
      _ = q ^ k * (z ^ m * (p ^ m * q)) := by rw [h.q_mul_p_pow]
      _ = z ^ m * (q ^ k * p ^ m) * q := by
        have : q ^ k * z ^ m = z ^ m * q ^ k :=
          (Commute.pow_pow (show Commute z q from h.zq) m k).eq.symm
        calc q ^ k * (z ^ m * (p ^ m * q)) = (q ^ k * z ^ m) * (p ^ m * q) := by group
          _ = z ^ m * q ^ k * (p ^ m * q) := by rw [this]
          _ = z ^ m * (q ^ k * p ^ m) * q := by group
      _ = z ^ m * (z ^ (k * m) * (p ^ m * q ^ k)) * q := by rw [ih]
      _ = z ^ ((k + 1) * m) * (p ^ m * q ^ (k + 1)) := by
        rw [show (k + 1) * m = m + k * m by ring, pow_add, pow_succ]; group

theorem nf_mul (i j k i' j' k' : ℕ) :
    (z ^ i * p ^ j * q ^ k) * (z ^ i' * p ^ j' * q ^ k') =
      z ^ (i + i' + k * j') * p ^ (j + j') * q ^ (k + k') := by
  have hc1 : q ^ k * z ^ i' = z ^ i' * q ^ k :=
    (Commute.pow_pow (show Commute z q from h.zq) i' k).eq.symm
  have hc2 : p ^ j * z ^ i' = z ^ i' * p ^ j :=
    (Commute.pow_pow (show Commute z p from h.zp) i' j).eq.symm
  have hz : z ^ (k * j') * p ^ j' = p ^ j' * z ^ (k * j') :=
    (Commute.pow_pow (show Commute z p from h.zp) (k * j') j').eq
  calc (z ^ i * p ^ j * q ^ k) * (z ^ i' * p ^ j' * q ^ k')
      = z ^ i * p ^ j * (q ^ k * z ^ i') * p ^ j' * q ^ k' := by group
    _ = z ^ i * p ^ j * (z ^ i' * q ^ k) * p ^ j' * q ^ k' := by rw [hc1]
    _ = z ^ i * (p ^ j * z ^ i') * (q ^ k * p ^ j') * q ^ k' := by group
    _ = z ^ i * (z ^ i' * p ^ j) * (z ^ (k * j') * (p ^ j' * q ^ k)) * q ^ k' := by
      rw [hc2, h.q_pow_mul_p_pow]
    _ = z ^ i * z ^ i' * (p ^ j * z ^ (k * j')) * p ^ j' * q ^ k * q ^ k' := by group
    _ = z ^ i * z ^ i' * (z ^ (k * j') * p ^ j) * p ^ j' * q ^ k * q ^ k' := by
      rw [(Commute.pow_pow (show Commute z p from h.zp) (k * j') j).eq.symm]
    _ = z ^ (i + i' + k * j') * p ^ (j + j') * q ^ (k + k') := by
      rw [pow_add z (i + i'), pow_add z i, pow_add p, pow_add q]; group

theorem p_four : p ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h.p_sq, h.z_sq]

theorem q_four : q ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h.q_sq, h.z_sq]

theorem mem_closure_iff {g : K} :
    g ∈ closure ({p, q} : Set K) ↔ ∃ i j k : ℕ, g = z ^ i * p ^ j * q ^ k := by
  constructor
  · intro hg
    refine closure_induction (p := fun g _ => ∃ i j k : ℕ, g = z ^ i * p ^ j * q ^ k)
      ?_ ⟨0, 0, 0, by simp⟩ ?_ ?_ hg
    · intro g hg
      rcases hg with rfl | rfl
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    · rintro g g' - - ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
      exact ⟨i + i' + k * j', j + j', k + k', h.nf_mul i j k i' j' k'⟩
    · rintro g - ⟨i, j, k, rfl⟩
      refine ⟨i + 9 * k * j, 3 * j, 3 * k, ?_⟩
      have hq : (q ^ k)⁻¹ = q ^ (3 * k) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 3 * k = 4 * k by ring, pow_mul, h.q_four,
          one_pow]
      have hp : (p ^ j)⁻¹ = p ^ (3 * j) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 3 * j = 4 * j by ring, pow_mul, h.p_four,
          one_pow]
      have hz : (z ^ i)⁻¹ = z ^ i := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, pow_mul, h.z_sq, one_pow]
      have hc : q ^ (3 * k) * p ^ (3 * j) = z ^ (3 * k * (3 * j)) * (p ^ (3 * j) * q ^ (3 * k)) :=
        h.q_pow_mul_p_pow _ _
      have hzq : z ^ i * p ^ 0 * q ^ 0 = z ^ i := by simp
      calc (z ^ i * p ^ j * q ^ k)⁻¹ = (q ^ k)⁻¹ * (p ^ j)⁻¹ * (z ^ i)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev]; group
        _ = q ^ (3 * k) * p ^ (3 * j) * z ^ i := by rw [hq, hp, hz]
        _ = (z ^ (3 * k * (3 * j)) * (p ^ (3 * j) * q ^ (3 * k))) * z ^ i := by rw [hc]
        _ = z ^ (i + 9 * k * j) * p ^ (3 * j) * q ^ (3 * k) := by
          have hzc : q ^ (3 * k) * z ^ i = z ^ i * q ^ (3 * k) :=
            (Commute.pow_pow (show Commute z q from h.zq) i (3 * k)).eq.symm
          calc (z ^ (3 * k * (3 * j)) * (p ^ (3 * j) * q ^ (3 * k))) * z ^ i
              = z ^ (3 * k * (3 * j)) * p ^ (3 * j) * (q ^ (3 * k) * z ^ i) := by group
            _ = z ^ (3 * k * (3 * j)) * p ^ (3 * j) * (z ^ i * q ^ (3 * k)) := by rw [hzc]
            _ = z ^ (3 * k * (3 * j)) * (p ^ (3 * j) * z ^ i) * q ^ (3 * k) := by group
            _ = z ^ (3 * k * (3 * j)) * (z ^ i * p ^ (3 * j)) * q ^ (3 * k) := by
              rw [(Commute.pow_pow (show Commute z p from h.zp) i (3 * j)).eq.symm]
            _ = z ^ (i + 9 * k * j) * p ^ (3 * j) * q ^ (3 * k) := by
              have : z ^ (3 * k * (3 * j)) * z ^ i = z ^ (i + 9 * k * j) := by
                rw [← pow_add, show 3 * k * (3 * j) + i = i + 9 * k * j by ring]
              calc z ^ (3 * k * (3 * j)) * (z ^ i * p ^ (3 * j)) * q ^ (3 * k)
                  = (z ^ (3 * k * (3 * j)) * z ^ i) * p ^ (3 * j) * q ^ (3 * k) := by group
                _ = _ := by rw [this]
  · rintro ⟨i, j, k, rfl⟩
    have hz : z ∈ closure ({p, q} : Set K) := by
      rw [← h.p_sq]; exact pow_mem (subset_closure (by simp)) 2
    exact mul_mem (mul_mem (pow_mem hz i) (pow_mem (subset_closure (by simp)) j))
      (pow_mem (subset_closure (by simp)) k)

theorem z_pow_mod (n : ℕ) : z ^ n = z ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, h.z_sq, one_pow, one_mul]

theorem eq_of_sq_eq_one {g : K} (hg : g ∈ closure ({p, q} : Set K)) (hg2 : g ^ 2 = 1) :
    g = 1 ∨ g = z := by
  obtain ⟨i, j, k, rfl⟩ := h.mem_closure_iff.mp hg
  have hsq := h.nf_mul i j k i j k
  rw [← sq, hg2] at hsq
  have hpj : p ^ (j + j) = z ^ j := by rw [← two_mul, pow_mul, h.p_sq]
  have hqk : q ^ (k + k) = z ^ k := by rw [← two_mul, pow_mul, h.q_sq]
  rw [hpj, hqk, ← pow_add, ← pow_add] at hsq
  have hpar : (i + i + k * j + j + k) % 2 = 0 := by
    rw [h.z_pow_mod] at hsq
    rcases Nat.mod_two_eq_zero_or_one (i + i + k * j + j + k) with h0 | h1
    · exact h0
    · rw [h1, pow_one] at hsq
      exact absurd hsq.symm h.z_ne_one
  have hj : j % 2 = 0 ∧ k % 2 = 0 := by
    rcases Nat.even_or_odd j with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases Nat.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩ <;> subst ha <;> subst hb <;>
      first
        | omega
        | (exfalso; ring_nf at hpar; omega)
  obtain ⟨a, ha⟩ : ∃ a, j = 2 * a := ⟨j / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, k = 2 * b := ⟨k / 2, by omega⟩
  have hg' : z ^ i * p ^ j * q ^ k = z ^ (i + a + b) := by
    rw [ha, hb, pow_mul p, pow_mul q, h.p_sq, h.q_sq, pow_add, pow_add]
  rw [hg', h.z_pow_mod]
  rcases Nat.mod_two_eq_zero_or_one (i + a + b) with h0 | h1
  · left; rw [h0, pow_zero]
  · right; rw [h1, pow_one]

theorem card_closure_le : Nat.card (closure ({p, q} : Set K)) ≤ 8 := by
  let f : Fin 2 × Fin 2 × Fin 2 → closure ({p, q} : Set K) := fun a =>
    ⟨z ^ a.1.val * p ^ a.2.1.val * q ^ a.2.2.val, h.mem_closure_iff.mpr ⟨_, _, _, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨i, j, k, rfl⟩ := h.mem_closure_iff.mp hg
    refine ⟨(⟨(i + j / 2 + k / 2) % 2, Nat.mod_lt _ (by norm_num)⟩,
      ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩, ⟨k % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    change z ^ ((i + j / 2 + k / 2) % 2) * p ^ (j % 2) * q ^ (k % 2) = z ^ i * p ^ j * q ^ k
    have hpj : p ^ j = z ^ (j / 2) * p ^ (j % 2) := by
      conv_lhs => rw [← Nat.div_add_mod j 2, pow_add, pow_mul, h.p_sq]
    have hqk : q ^ k = z ^ (k / 2) * q ^ (k % 2) := by
      conv_lhs => rw [← Nat.div_add_mod k 2, pow_add, pow_mul, h.q_sq]
    have hc1 : p ^ (j % 2) * z ^ (k / 2) = z ^ (k / 2) * p ^ (j % 2) :=
      (Commute.pow_pow (show Commute z p from h.zp) (k / 2) (j % 2)).eq.symm
    rw [← h.z_pow_mod]
    calc z ^ (i + j / 2 + k / 2) * p ^ (j % 2) * q ^ (k % 2)
        = z ^ i * z ^ (j / 2) * (z ^ (k / 2) * p ^ (j % 2)) * q ^ (k % 2) := by
          rw [pow_add, pow_add]; group
      _ = z ^ i * z ^ (j / 2) * (p ^ (j % 2) * z ^ (k / 2)) * q ^ (k % 2) := by rw [← hc1]
      _ = z ^ i * (z ^ (j / 2) * p ^ (j % 2)) * (z ^ (k / 2) * q ^ (k % 2)) := by group
      _ = z ^ i * p ^ j * q ^ k := by rw [← hpj, ← hqk]
  calc Nat.card (closure ({p, q} : Set K)) ≤ Nat.card (Fin 2 × Fin 2 × Fin 2) :=
        Nat.card_le_card_of_surjective f hf
    _ = 8 := by simp

end Q8Rel

end Q8

end CFSG.LocalAnalysis.EvenBN.Tits.I21
