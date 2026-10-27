module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup

section Rel

variable {G : Type*} [Group G] {t u x : G}

structure CRel (t u x : G) : Prop where
  t_sq : t ^ 2 = 1
  u_four : u ^ 4 = 1
  x_five : x ^ 5 = 1
  tu : t * u = u * t
  tx : t * x = x * t
  ux : u * x * u⁻¹ = x ^ 2
  t_ne_one : t ≠ 1
  z_ne_one : u ^ 2 ≠ 1
  z_ne_t : u ^ 2 ≠ t

theorem pow_mod_of_pow_eq_one {g : G} {n : ℕ} (hg : g ^ n = 1) (k : ℕ) :
    g ^ k = g ^ (k % n) := by
  conv_lhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hg, one_pow, one_mul]

theorem two_pow_mod_five (j : ℕ) : 2 ^ j % 5 = 2 ^ (j % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod j 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

namespace CRel

variable (h : CRel t u x)

include h

theorem u_conj_pow (n : ℕ) : u * x ^ n * u⁻¹ = x ^ (2 * n) := by
  rw [← conj_pow, h.ux, ← pow_mul, mul_comm]

theorem pow_u_mul_x_pow (j i : ℕ) : u ^ j * x ^ i = x ^ (i * 2 ^ j) * u ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc u ^ (j + 1) * x ^ i = u * (u ^ j * x ^ i) := by rw [pow_succ', mul_assoc]
      _ = u * (x ^ (i * 2 ^ j) * u ^ j) := by rw [ih]
      _ = (u * x ^ (i * 2 ^ j) * u⁻¹) * (u * u ^ j) := by group
      _ = x ^ (i * 2 ^ (j + 1)) * u ^ (j + 1) := by
        rw [h.u_conj_pow, ← pow_succ', show 2 * (i * 2 ^ j) = i * 2 ^ (j + 1) by ring]

theorem t_comm_x_pow (i : ℕ) : t * x ^ i = x ^ i * t :=
  ((Commute.pow_right (show Commute t x from h.tx) i)).eq

theorem nf_mul (a i j b k l : ℕ) :
    (t ^ a * x ^ i * u ^ j) * (t ^ b * x ^ k * u ^ l) =
      t ^ (a + b) * x ^ (i + k * 2 ^ j) * u ^ (j + l) := by
  have hub : u ^ j * t ^ b = t ^ b * u ^ j :=
    (Commute.pow_pow (show Commute t u from h.tu) b j).eq.symm
  have hxb : x ^ i * t ^ b = t ^ b * x ^ i :=
    (Commute.pow_pow (show Commute t x from h.tx) b i).eq.symm
  calc (t ^ a * x ^ i * u ^ j) * (t ^ b * x ^ k * u ^ l)
      = t ^ a * x ^ i * ((u ^ j * t ^ b) * x ^ k * u ^ l) := by group
    _ = t ^ a * x ^ i * (t ^ b * (u ^ j * x ^ k) * u ^ l) := by rw [hub]; group
    _ = t ^ a * x ^ i * (t ^ b * (x ^ (k * 2 ^ j) * u ^ j) * u ^ l) := by
      rw [h.pow_u_mul_x_pow j k]
    _ = t ^ a * (x ^ i * t ^ b) * x ^ (k * 2 ^ j) * u ^ j * u ^ l := by group
    _ = t ^ a * (t ^ b * x ^ i) * x ^ (k * 2 ^ j) * u ^ j * u ^ l := by rw [hxb]
    _ = t ^ (a + b) * x ^ (i + k * 2 ^ j) * u ^ (j + l) := by
      rw [pow_add, pow_add, pow_add]; group

theorem nf_inv (a i j : ℕ) :
    (t ^ a * x ^ i * u ^ j)⁻¹ = t ^ a * x ^ (4 * i * 2 ^ (3 * j)) * u ^ (3 * j) := by
  have hx4 : (x ^ i)⁻¹ = x ^ (4 * i) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    have : x ^ (i + 4 * i) = (x ^ 5) ^ i := by rw [← pow_mul]; ring_nf
    rw [this, h.x_five, one_pow]
  have hu3 : (u ^ j)⁻¹ = u ^ (3 * j) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    have : u ^ (j + 3 * j) = (u ^ 4) ^ j := by rw [← pow_mul]; ring_nf
    rw [this, h.u_four, one_pow]
  have ht : (t ^ a)⁻¹ = t ^ a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    have : t ^ (a + a) = (t ^ 2) ^ a := by rw [← pow_mul]; ring_nf
    rw [this, h.t_sq, one_pow]
  have := h.nf_mul 0 0 (3 * j) 0 (4 * i) 0
  have h2 := h.nf_mul 0 (0 + 4 * i * 2 ^ (3 * j)) (3 * j) a 0 0
  simp only [pow_zero, mul_one, one_mul, zero_add, add_zero, zero_mul] at this h2
  rw [mul_inv_rev, mul_inv_rev, hu3, hx4, ht]
  rw [← mul_assoc, this, h2]

theorem mem_closure_iff {g : G} :
    g ∈ closure ({t, u, x} : Set G) ↔ ∃ a i j : ℕ, g = t ^ a * x ^ i * u ^ j := by
  constructor
  · intro hg
    refine closure_induction (p := fun g _ => ∃ a i j : ℕ, g = t ^ a * x ^ i * u ^ j)
      ?_ ⟨0, 0, 0, by simp⟩ ?_ ?_ hg
    · intro g hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
    · rintro g g' - - ⟨a, i, j, rfl⟩ ⟨b, k, l, rfl⟩
      exact ⟨a + b, i + k * 2 ^ j, j + l, h.nf_mul a i j b k l⟩
    · rintro g - ⟨a, i, j, rfl⟩
      exact ⟨a, 4 * i * 2 ^ (3 * j), 3 * j, h.nf_inv a i j⟩
  · rintro ⟨a, i, j, rfl⟩
    exact mul_mem (mul_mem (pow_mem (subset_closure (by simp)) a)
      (pow_mem (subset_closure (by simp)) i)) (pow_mem (subset_closure (by simp)) j)

theorem orderOf_u : orderOf u = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h.z_ne_one) (by simpa using h.u_four)

theorem x_pow_eq_one_of_mul_eq_one {a i j : ℕ} (hg : t ^ a * x ^ i * u ^ j = 1) :
    x ^ i = 1 := by
  have hc : t ^ a * x ^ i = x ^ i * t ^ a :=
    (Commute.pow_pow (show Commute t x from h.tx) a i).eq
  have hr : x ^ i * (t ^ a * u ^ j) = 1 := by
    rw [← hg, hc]; group
  have ht8 : (t ^ a) ^ 8 = 1 := by
    rw [← pow_mul, show a * 8 = 2 * (4 * a) by ring, pow_mul, h.t_sq, one_pow]
  have hu8 : (u ^ j) ^ 8 = 1 := by
    rw [← pow_mul, show j * 8 = 4 * (2 * j) by ring, pow_mul, h.u_four, one_pow]
  have h8r : (t ^ a * u ^ j) ^ 8 = 1 := by
    rw [(Commute.pow_pow (show Commute t u from h.tu) a j).mul_pow, ht8, hu8, one_mul]
  have h8 : (x ^ i) ^ 8 = 1 := by
    rw [eq_inv_of_mul_eq_one_left hr, inv_pow, h8r, inv_one]
  have h5 : (x ^ i) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h.x_five, one_pow]
  have := (pow_gcd_eq_one (a := x ^ i) (m := 5) (n := 8)).2 ⟨h5, h8⟩
  simpa using this

theorem nf_eq_one_iff {a i j : ℕ} :
    t ^ a * x ^ i * u ^ j = 1 ↔ 2 ∣ a ∧ x ^ i = 1 ∧ 4 ∣ j := by
  constructor
  · intro hg
    have hx := h.x_pow_eq_one_of_mul_eq_one hg
    rw [hx, mul_one] at hg
    have hcu : t ^ a * u ^ j = 1 := hg
    have ha2 : 2 ∣ a := by
      by_contra hodd
      obtain ⟨k, hk⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
      have hta : t ^ a = t := by
        rw [hk, pow_succ, pow_mul, h.t_sq, one_pow, one_mul]
      rw [hta] at hcu
      have h2 : t = (u ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hcu
      have hu2 : (u ^ j) ^ 2 = 1 := by
        have : t ^ 2 = 1 := h.t_sq
        rw [h2, inv_pow] at this
        exact inv_eq_one.mp this
      have hj2 : 2 ∣ j := by
        have : (u ^ 4) = 1 := h.u_four
        by_contra hj
        obtain ⟨m, hm⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have h1 : u ^ (2 * j) = 1 := by rw [mul_comm, pow_mul]; exact hu2
        have h4 : u ^ (2 * (2 * m + 1)) = u ^ 2 := by
          rw [show 2 * (2 * m + 1) = 4 * m + 2 by ring, pow_add, pow_mul, h.u_four, one_pow,
            one_mul]
        rw [hm] at h1
        exact h.z_ne_one (h4 ▸ h1)
      obtain ⟨m, hm⟩ := hj2
      have hum : u ^ j = 1 ∨ u ^ j = u ^ 2 := by
        rw [hm]
        rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
        · left
          rw [hn, show 2 * (n + n) = 4 * n by ring, pow_mul, h.u_four, one_pow]
        · right
          rw [hn, show 2 * (2 * n + 1) = 4 * n + 2 by ring, pow_add, pow_mul, h.u_four, one_pow,
            one_mul]
      rcases hum with hum | hum
      · rw [hum, inv_one] at h2
        exact h.t_ne_one h2
      · rw [hum] at h2
        have hzinv : (u ^ 2)⁻¹ = u ^ 2 := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show 2 + 2 = 4 by rfl, h.u_four]
        rw [hzinv] at h2
        exact h.z_ne_t h2.symm
    refine ⟨ha2, hx, ?_⟩
    obtain ⟨k, hk⟩ := ha2
    have : t ^ a = 1 := by rw [hk, pow_mul, h.t_sq, one_pow]
    rw [this, one_mul] at hcu
    exact h.orderOf_u ▸ orderOf_dvd_of_pow_eq_one hcu
  · rintro ⟨⟨k, hk⟩, hx, ⟨m, hm⟩⟩
    rw [hx, hk, hm, mul_one, pow_mul, pow_mul, h.t_sq, h.u_four, one_pow, one_pow, one_mul]

theorem x_pow_two_pow (i j : ℕ) : x ^ (i * 2 ^ j) = x ^ (i * 2 ^ (j % 4)) := by
  rw [pow_mod_of_pow_eq_one h.x_five (i * 2 ^ j), pow_mod_of_pow_eq_one h.x_five
    (i * 2 ^ (j % 4)), Nat.mul_mod, two_pow_mod_five, ← Nat.mul_mod]

theorem eq_of_sq_eq_one {s : G} (hs : s ∈ closure ({t, u, x} : Set G)) (hs2 : s ^ 2 = 1)
    (hs1 : s ≠ 1) : s = t ∨ (∃ i : ℕ, s = x ^ i * u ^ 2) ∨ ∃ i : ℕ, s = t * (x ^ i * u ^ 2) := by
  obtain ⟨a, i, j, rfl⟩ := h.mem_closure_iff.mp hs
  have hsq : (t ^ a * x ^ i * u ^ j) * (t ^ a * x ^ i * u ^ j) = 1 := by rw [← sq]; exact hs2
  rw [h.nf_mul, h.nf_eq_one_iff] at hsq
  obtain ⟨-, hx, hj⟩ := hsq
  have hj2 : j % 4 = 0 ∨ j % 4 = 2 := by omega
  have hta : t ^ a = 1 ∨ t ^ a = t := by
    rw [pow_mod_of_pow_eq_one h.t_sq a]
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · left; rw [h0, pow_zero]
    · right; rw [h1, pow_one]
  rcases hj2 with h0 | h2
  ·
    have hu : u ^ j = 1 := by
      rw [pow_mod_of_pow_eq_one h.u_four j, h0, pow_zero]
    have hx2 : x ^ i = 1 := by
      rw [pow_add, h.x_pow_two_pow i j, h0, pow_zero, mul_one, ← pow_two] at hx
      have h5 : (x ^ i) ^ 5 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, h.x_five, one_pow]
      have := (pow_gcd_eq_one (a := x ^ i) (m := 2) (n := 5)).2 ⟨hx, h5⟩
      simpa using this
    rw [hu, hx2] at hs1 ⊢
    rcases hta with h1 | h1
    · exact absurd (by simp [h1]) hs1
    · left; simp [h1]
  · have hu : u ^ j = u ^ 2 := by
      rw [pow_mod_of_pow_eq_one h.u_four j, h2]
    rw [hu]
    rcases hta with h1 | h1
    · right; left; exact ⟨i, by rw [h1, one_mul]⟩
    · right; right; exact ⟨i, by rw [h1, mul_assoc]⟩

end CRel

end Rel

end CFSG.LocalAnalysis.EvenBN.Tits.I21
