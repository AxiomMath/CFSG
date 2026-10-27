module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Coprime.Lemmas

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup

section Dih

variable {K : Type*} [Group K] {t x : K}

structure DihRel (t x : K) : Prop where
  t_sq : t ^ 2 = 1
  tx : t * x * t⁻¹ = x⁻¹

section Order

variable {n : ℕ}

theorem z_sq (hx : orderOf x = 2 ^ (n - 1)) (hn : 2 ≤ n) : (x ^ 2 ^ (n - 2)) ^ 2 = 1 := by
  rw [← pow_mul, ← pow_succ, show n - 2 + 1 = n - 1 by omega, ← hx]
  exact pow_orderOf_eq_one x

theorem z_ne_one (hx : orderOf x = 2 ^ (n - 1)) (hn : 2 ≤ n) : x ^ 2 ^ (n - 2) ≠ 1 := by
  intro h1
  have h0 := orderOf_dvd_of_pow_eq_one h1
  rw [hx] at h0
  have h2 := Nat.le_of_dvd (pow_pos (by norm_num) _) h0
  have h3 : 2 ^ (n - 2) < 2 ^ (n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem eq_one_or_eq_z_of_sq_eq_one (hx : orderOf x = 2 ^ (n - 1)) (hn : 2 ≤ n) (k : ℤ)
    (hk : (x ^ k) ^ 2 = 1) : x ^ k = 1 ∨ x ^ k = x ^ 2 ^ (n - 2) := by
  have h1 : x ^ (k * 2) = 1 := by rw [zpow_mul, zpow_ofNat]; exact hk
  have h2 : ((2 ^ (n - 1) : ℕ) : ℤ) ∣ k * 2 := by
    rw [← hx]; exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h3 : ((2 ^ (n - 2) : ℕ) : ℤ) ∣ k := by
    have : (2 ^ (n - 1) : ℕ) = 2 ^ (n - 2) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this] at h2
    push_cast at h2 ⊢
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).mp h2
  obtain ⟨j, hj⟩ := h3
  have hz2 := z_sq hx hn
  have hzj : x ^ k = (x ^ 2 ^ (n - 2)) ^ j := by
    rw [hj, ← zpow_natCast, ← zpow_mul]
  rw [hzj]
  rcases Int.even_or_odd j with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_ofNat, hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hz2, one_zpow, one_mul, zpow_one]

end Order

namespace DihRel

variable (d : DihRel t x)

include d

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact d.t_sq)

theorem t_mul_t : t * t = 1 := by rw [← sq]; exact d.t_sq

theorem t_zpow (k : ℤ) : t * x ^ k * t⁻¹ = x ^ (-k) := by
  rw [← conj_zpow, d.tx, inv_zpow']

theorem t_mul_zpow (k : ℤ) : t * x ^ k = x ^ (-k) * t := by
  rw [← d.t_zpow k]; group

theorem zpow_mul_t (k : ℤ) : x ^ k * t = t * x ^ (-k) := by
  rw [d.t_mul_zpow (-k), neg_neg]

theorem mem_closure_iff {g : K} :
    g ∈ closure ({t, x} : Set K) ↔ (∃ k : ℤ, g = x ^ k) ∨ ∃ k : ℤ, g = t * x ^ k := by
  constructor
  · intro hg
    refine closure_induction (p := fun g _ => (∃ k : ℤ, g = x ^ k) ∨ ∃ k : ℤ, g = t * x ^ k)
      ?_ (Or.inl ⟨0, by simp⟩) ?_ ?_ hg
    · intro g hg
      rcases hg with rfl | rfl
      · exact Or.inr ⟨0, by simp⟩
      · exact Or.inl ⟨1, by simp⟩
    · rintro g g' - - (⟨k, rfl⟩ | ⟨k, rfl⟩) (⟨l, rfl⟩ | ⟨l, rfl⟩)
      · exact Or.inl ⟨k + l, by rw [zpow_add]⟩
      · exact Or.inr ⟨l - k, by
          calc x ^ k * (t * x ^ l) = (x ^ k * t) * x ^ l := by group
            _ = (t * x ^ (-k)) * x ^ l := by rw [d.zpow_mul_t]
            _ = t * x ^ (l - k) := by rw [mul_assoc, ← zpow_add]; ring_nf⟩
      · exact Or.inr ⟨k + l, by rw [mul_assoc, ← zpow_add]⟩
      · exact Or.inl ⟨l - k, by
          calc t * x ^ k * (t * x ^ l) = t * (x ^ k * t) * x ^ l := by group
            _ = t * (t * x ^ (-k)) * x ^ l := by rw [d.zpow_mul_t]
            _ = (t * t) * (x ^ (-k) * x ^ l) := by group
            _ = x ^ (l - k) := by rw [d.t_mul_t, one_mul, ← zpow_add]; ring_nf⟩
    · rintro g - (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · exact Or.inl ⟨-k, by rw [zpow_neg]⟩
      · exact Or.inr ⟨k, by
          rw [mul_inv_rev, d.t_inv, ← zpow_neg, d.zpow_mul_t, neg_neg]⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact zpow_mem (subset_closure (by simp)) k
    · exact mul_mem (subset_closure (by simp)) (zpow_mem (subset_closure (by simp)) k)

theorem refl_sq (k : ℤ) : (t * x ^ k) ^ 2 = 1 := by
  rw [pow_two]
  calc t * x ^ k * (t * x ^ k) = (t * x ^ k) * t * x ^ k := by group
    _ = (x ^ (-k) * t) * t * x ^ k := by rw [d.t_mul_zpow k]
    _ = x ^ (-k) * (t * t) * x ^ k := by group
    _ = 1 := by rw [d.t_mul_t, mul_one, ← zpow_add]; simp

theorem conj_t_x_zpow (j : ℤ) : x ^ j * t * (x ^ j)⁻¹ = t * x ^ (-(2 * j)) := by
  calc x ^ j * t * (x ^ j)⁻¹ = (x ^ j * t) * x ^ (-j) := by rw [zpow_neg]
    _ = (t * x ^ (-j)) * x ^ (-j) := by rw [d.zpow_mul_t]
    _ = t * x ^ (-(2 * j)) := by rw [mul_assoc, ← zpow_add]; ring_nf

theorem refl_conj_rot (i k : ℤ) : (t * x ^ i) * x ^ k * (t * x ^ i)⁻¹ = x ^ (-k) := by
  calc (t * x ^ i) * x ^ k * (t * x ^ i)⁻¹ = t * (x ^ i * x ^ k * x ^ (-i)) * t⁻¹ := by
        rw [mul_inv_rev, zpow_neg]; group
    _ = t * x ^ k * t⁻¹ := by rw [← zpow_add, ← zpow_add]; ring_nf
    _ = x ^ (-k) := d.t_zpow k

theorem commute_zpow_iff (k : ℤ) : t * x ^ k = x ^ k * t ↔ (x ^ k) ^ 2 = 1 := by
  rw [d.t_mul_zpow k]
  constructor
  · intro h
    have h1 : x ^ (-k) = x ^ k := mul_right_cancel h
    have h2 : x ^ k * x ^ k = 1 := by
      calc x ^ k * x ^ k = x ^ k * x ^ (-k) := by rw [h1]
        _ = 1 := by rw [← zpow_add]; simp
    rw [pow_two]
    exact h2
  · intro h
    have h' : x ^ k * x ^ k = 1 := by rw [← pow_two]; exact h
    have h3 : x ^ (-k) = x ^ k := by
      rw [zpow_neg]
      exact inv_eq_of_mul_eq_one_right h'
    rw [h3]

theorem ext_step {n : ℕ} (hx : orderOf x = 2 ^ (n - 1)) (hn : 3 ≤ n) {s : K} (hs : s ^ 2 = 1)
    {a : ℤ} (ha : Odd a) (hsa : s * t * s⁻¹ = t * x ^ a) :
    DihRel t (s * t) ∧ orderOf (s * t) = 2 ^ n ∧ (s * t) ^ 2 ^ (n - 1) = x ^ 2 ^ (n - 2) ∧
      x ∈ zpowers (s * t) := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hs)
  have hsts : s * t * s = t * x ^ a := by rw [← hsa, hs_inv]
  have hsq : (s * t) ^ 2 = x ^ (-a) := by
    calc (s * t) ^ 2 = (s * t * s) * t := by rw [pow_two]; group
      _ = (t * x ^ a) * t := by rw [hsts]
      _ = t * x ^ a * t⁻¹ := by rw [d.t_inv]
      _ = x ^ (-a) := d.t_zpow a
  have hz2 : (x ^ 2 ^ (n - 2)) ^ 2 = 1 := z_sq hx (by omega)
  have hz1 : x ^ 2 ^ (n - 2) ≠ 1 := z_ne_one hx (by omega)
  have hzodd : (x ^ 2 ^ (n - 2)) ^ (-a) = x ^ 2 ^ (n - 2) := by
    obtain ⟨c, rfl⟩ := ha
    have hzi : (x ^ 2 ^ (n - 2))⁻¹ = x ^ 2 ^ (n - 2) :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
    have h2c : (x ^ 2 ^ (n - 2)) ^ (2 * c) = 1 := by rw [zpow_mul, zpow_ofNat, hz2, one_zpow]
    calc (x ^ 2 ^ (n - 2)) ^ (-(2 * c + 1)) = (x ^ 2 ^ (n - 2)) ^ (-(2 * c) + -1) := by
          congr 1; ring
      _ = x ^ 2 ^ (n - 2) := by
          rw [zpow_add, zpow_neg, h2c, inv_one, one_mul, zpow_neg_one, hzi]
  have hpow : (s * t) ^ 2 ^ (n - 1) = x ^ 2 ^ (n - 2) := by
    calc (s * t) ^ 2 ^ (n - 1) = ((s * t) ^ 2) ^ 2 ^ (n - 2) := by
          rw [← pow_mul, ← pow_succ']; congr 2; omega
      _ = (x ^ (-a)) ^ 2 ^ (n - 2) := by rw [hsq]
      _ = (x ^ 2 ^ (n - 2)) ^ (-a) := by
          rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast x, ← zpow_mul]
          congr 1
          push_cast
          ring
      _ = x ^ 2 ^ (n - 2) := hzodd
  have hord : orderOf (s * t) = 2 ^ n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : orderOf (s * t) = 2 ^ (n - 1 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := n - 1) (by rw [hpow]; exact hz1)
        (by rw [pow_succ, pow_mul, hpow]; exact hz2)
    rw [h1]; congr 1; omega
  refine ⟨⟨d.t_sq, ?_⟩, hord, hpow, ?_⟩
  · calc t * (s * t) * t⁻¹ = t * s := by group
      _ = (s * t)⁻¹ := by rw [mul_inv_rev, d.t_inv, hs_inv]
  · have hcop : IsCoprime a ((2 : ℤ) ^ (n - 1)) := (Odd.isCoprime_two ha).pow_right
    obtain ⟨u, v, huv⟩ := hcop
    have hxn : x ^ ((2 : ℤ) ^ (n - 1)) = 1 := by
      rw [show ((2 : ℤ) ^ (n - 1)) = ((2 ^ (n - 1) : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, ← hx]
      exact pow_orderOf_eq_one x
    have hxa : x ^ (-a) ∈ zpowers (s * t) := by
      rw [← hsq]; exact pow_mem (mem_zpowers _) 2
    have hxa' : x ^ a ∈ zpowers (s * t) := by
      have := inv_mem hxa
      rwa [← zpow_neg, neg_neg] at this
    have h1 : x ^ (v * (2 : ℤ) ^ (n - 1)) = 1 := by rw [mul_comm, zpow_mul, hxn, one_zpow]
    have h2 : x ^ (u * a) = (x ^ a) ^ u := by rw [mul_comm, zpow_mul]
    have hxe : x = (x ^ a) ^ u := by
      calc x = x ^ (u * a + v * (2 : ℤ) ^ (n - 1)) := by rw [huv, zpow_one]
        _ = x ^ (u * a) * x ^ (v * (2 : ℤ) ^ (n - 1)) := zpow_add _ _ _
        _ = (x ^ a) ^ u := by rw [h1, h2, mul_one]
    have := zpow_mem hxa' u
    rwa [← hxe] at this

end DihRel

section NRel

variable {K : Type*} [Group K] {t w v : K}

structure NRel (t w v : K) : Prop where
  t_sq : t ^ 2 = 1
  w_four : w ^ 4 = 1
  v_sq : v ^ 2 = 1
  tw : t * w = w * t
  vw : v * w = w * v
  vt : v * t * v⁻¹ = t * w ^ 2

namespace NRel

variable (d : NRel t w v)

include d

theorem w_pow_t_pow (j k : ℕ) : w ^ j * t ^ k = t ^ k * w ^ j :=
  (Commute.pow_pow (show Commute t w from d.tw) k j).eq.symm

theorem v_pow_w_pow (c j : ℕ) : v ^ c * w ^ j = w ^ j * v ^ c :=
  (Commute.pow_pow (show Commute v w from d.vw) c j).eq

theorem v_t : v * t = t * w ^ 2 * v := by
  have := d.vt
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem v_t_pow (a : ℕ) : v * t ^ a = t ^ a * w ^ (2 * a) * v := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc v * t ^ (a + 1) = (v * t ^ a) * t := by rw [pow_succ]; group
      _ = t ^ a * w ^ (2 * a) * (v * t) := by rw [ih]; group
      _ = t ^ a * w ^ (2 * a) * (t * w ^ 2 * v) := by rw [d.v_t]
      _ = t ^ a * (w ^ (2 * a) * t) * w ^ 2 * v := by group
      _ = t ^ a * (t * w ^ (2 * a)) * w ^ 2 * v := by
        rw [show w ^ (2 * a) * t = t * w ^ (2 * a) by simpa using d.w_pow_t_pow (2 * a) 1]
      _ = t ^ (a + 1) * w ^ (2 * (a + 1)) * v := by
        rw [show 2 * (a + 1) = 2 * a + 2 by ring, pow_succ, pow_add]; group

theorem v_pow_t_pow (c a : ℕ) : v ^ c * t ^ a = t ^ a * w ^ (2 * c * a) * v ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    calc v ^ (c + 1) * t ^ a = v ^ c * (v * t ^ a) := by rw [pow_succ, mul_assoc]
      _ = v ^ c * (t ^ a * w ^ (2 * a) * v) := by rw [d.v_t_pow]
      _ = (v ^ c * t ^ a) * w ^ (2 * a) * v := by group
      _ = t ^ a * w ^ (2 * c * a) * v ^ c * w ^ (2 * a) * v := by rw [ih]
      _ = t ^ a * w ^ (2 * c * a) * (v ^ c * w ^ (2 * a)) * v := by group
      _ = t ^ a * w ^ (2 * c * a) * (w ^ (2 * a) * v ^ c) * v := by rw [d.v_pow_w_pow]
      _ = t ^ a * (w ^ (2 * c * a) * w ^ (2 * a)) * (v ^ c * v) := by group
      _ = t ^ a * w ^ (2 * (c + 1) * a) * v ^ (c + 1) := by
        rw [← pow_add, pow_succ]; congr 3; ring

theorem nf_mul (a b c a' b' c' : ℕ) :
    (t ^ a * w ^ b * v ^ c) * (t ^ a' * w ^ b' * v ^ c') =
      t ^ (a + a') * w ^ (b + b' + 2 * c * a') * v ^ (c + c') := by
  calc (t ^ a * w ^ b * v ^ c) * (t ^ a' * w ^ b' * v ^ c')
      = t ^ a * w ^ b * (v ^ c * t ^ a') * w ^ b' * v ^ c' := by group
    _ = t ^ a * w ^ b * (t ^ a' * w ^ (2 * c * a') * v ^ c) * w ^ b' * v ^ c' := by
      rw [d.v_pow_t_pow]
    _ = t ^ a * (w ^ b * t ^ a') * w ^ (2 * c * a') * (v ^ c * w ^ b') * v ^ c' := by group
    _ = t ^ a * (t ^ a' * w ^ b) * w ^ (2 * c * a') * (w ^ b' * v ^ c) * v ^ c' := by
      rw [d.w_pow_t_pow, d.v_pow_w_pow]
    _ = (t ^ a * t ^ a') * (w ^ b * w ^ (2 * c * a') * w ^ b') * (v ^ c * v ^ c') := by group
    _ = t ^ (a + a') * w ^ (b + b' + 2 * c * a') * v ^ (c + c') := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 2; ring

theorem nf_sq (a b c : ℕ) : (t ^ a * w ^ b * v ^ c) ^ 2 = w ^ (2 * (b + c * a)) := by
  rw [pow_two, d.nf_mul]
  have h1 : t ^ (a + a) = 1 := by rw [← two_mul, pow_mul, d.t_sq, one_pow]
  have h2 : v ^ (c + c) = 1 := by rw [← two_mul, pow_mul, d.v_sq, one_pow]
  rw [h1, h2, one_mul, mul_one]
  congr 1; ring

end NRel

end NRel

end Dih

end CFSG.LocalAnalysis.EvenBN.Tits.I21
