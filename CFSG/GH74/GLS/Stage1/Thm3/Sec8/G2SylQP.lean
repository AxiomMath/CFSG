module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylDefs
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

open Subgroup

section Defs

variable {G : Type*} [Group G]

@[expose] def qpT (n : ℕ) (w₁ h : G) : G := w₁ * h ^ (2 ^ (n - 1))

@[expose] def qpY (w₁ w₂ : G) : G := w₁ * w₂

@[expose] def qpA (n : ℕ) (w₁ h : G) : Subgroup G :=
  Subgroup.zpowers h ⊔ Subgroup.zpowers ((qpT n w₁ h)⁻¹ * h * qpT n w₁ h)

@[expose] def qpS (n : ℕ) (w₁ w₂ h : G) : Subgroup G :=
  qpA n w₁ h ⊔ Subgroup.zpowers (qpT n w₁ h) ⊔ Subgroup.zpowers (qpY w₁ w₂)

end Defs

namespace QPShape

section Generic

variable {G : Type*} [Group G]

theorem two_pow_aux {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) ∧ 2 ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  rw [h1, h2]
  constructor <;> ring

theorem mem_zpowers_sup_iff {a b : G} (hab : Commute a b) {x : G} :
    x ∈ zpowers a ⊔ zpowers b ↔ ∃ i j : ℤ, a ^ i * b ^ j = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
        exact ⟨i, 0, by simp⟩
      · obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact ⟨0, j, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨i, j, rfl⟩ := ihx
      obtain ⟨i', j', rfl⟩ := ihy
      refine ⟨i + i', j + j', ?_⟩
      have hc : Commute (b ^ j) (a ^ i') := (hab.symm.zpow_zpow j i')
      rw [zpow_add, zpow_add]
      simp only [mul_assoc]
      rw [← mul_assoc (b ^ j) (a ^ i'), hc.eq, mul_assoc]
    | inv x hx ih =>
      obtain ⟨i, j, rfl⟩ := ih
      refine ⟨-i, -j, ?_⟩
      have hc : Commute (b ^ (-j)) (a ^ (-i)) := (hab.symm.zpow_zpow (-j) (-i))
      rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
      exact hc.eq.symm
  · rintro ⟨i, j, rfl⟩
    exact mul_mem_sup (zpow_mem (mem_zpowers a) i) (zpow_mem (mem_zpowers b) j)

theorem pow_odd_of_mul_self_eq_one {x : G} (hx : x * x = 1) {s : ℕ} (hs : Odd s) :
    x ^ s = x := by
  obtain ⟨r, rfl⟩ := hs
  rw [pow_succ, pow_mul, sq, hx, one_pow, one_mul]

theorem pow_eq_one_of_mul_self_eq_one {x : G} (hx : x * x = 1) {k : ℕ} (hk : Even k) :
    x ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [← two_mul, pow_mul, sq, hx, one_pow]

theorem mul_self_eq_one_of_mem_zpowers {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x * x = 1 := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz, one_zpow]

theorem pow_mul_of_mul_eq {h w e : G} (hhe : Commute h e) (hw : h * w = e * w * h) (k : ℕ) :
    h ^ k * w = e ^ k * w * h ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : h * e ^ k = e ^ k * h := (hhe.pow_right k).eq
    calc h ^ (k + 1) * w = h * (h ^ k * w) := by rw [pow_succ', mul_assoc]
      _ = h * (e ^ k * w * h ^ k) := by rw [ih]
      _ = (h * e ^ k) * w * h ^ k := by simp only [mul_assoc]
      _ = (e ^ k * h) * w * h ^ k := by rw [hk]
      _ = e ^ k * (h * w) * h ^ k := by simp only [mul_assoc]
      _ = e ^ k * (e * w * h) * h ^ k := by rw [hw]
      _ = e ^ (k + 1) * w * h ^ (k + 1) := by rw [pow_succ, pow_succ']; simp only [mul_assoc]

theorem inv_conj_of_conj {w c : G} (h : w * c * w⁻¹ = c⁻¹) : w⁻¹ * c * w = c⁻¹ := by
  have h2 : c = w⁻¹ * c⁻¹ * w := by
    calc c = w⁻¹ * (w * c * w⁻¹) * w := by group
      _ = w⁻¹ * c⁻¹ * w := by rw [h]
  calc w⁻¹ * c * w = (w⁻¹ * c⁻¹ * w)⁻¹ := by group
    _ = c⁻¹ := by rw [← h2]

theorem inv_conj_pow {w c : G} (h : w⁻¹ * c * w = c⁻¹) (s : ℕ) :
    w⁻¹ * c ^ s * w = (c ^ s)⁻¹ := by
  have := conj_pow (a := w⁻¹) (b := c) (i := s)
  rw [inv_inv] at this
  rw [← this, h, inv_pow]

theorem not_commute_of_conj {w c : G} (hw : w * c * w⁻¹ = c⁻¹) (hc : c * c ≠ 1) :
    ¬ (c * w = w * c) := by
  intro hcw
  apply hc
  have h1 : w * c * w⁻¹ = c := by rw [← hcw, mul_assoc, mul_inv_cancel, mul_one]
  rw [h1] at hw
  exact mul_eq_one_iff_eq_inv.mpr hw

theorem t_sq_aux {w P z : G} (hz : z * z = 1) (hwz : w * z = z * w) (hww : w * w = z)
    (hP : P * w = z * w * P) (hPP : P * P = 1) : (w * P) * (w * P) = 1 := by
  calc (w * P) * (w * P) = w * (P * w) * P := by simp only [mul_assoc]
    _ = w * (z * w * P) * P := by rw [hP]
    _ = (w * z) * w * (P * P) := by simp only [mul_assoc]
    _ = (z * w) * w * 1 := by rw [hwz, hPP]
    _ = z * (w * w) := by simp only [mul_assoc, mul_one]
    _ = 1 := by rw [hww, hz]

theorem ty_aux {w₁ w₂ P z : G} (hz : z * z = 1) (hw₁z : w₁ * z = z * w₁) (hw₁ : w₁ * w₁ = z)
    (hw : w₁ * w₂ = w₂ * w₁) (hP₁ : P * w₁ = z * w₁ * P) (hP₂ : P * w₂ = z * w₂ * P) :
    (w₁ * P) * (w₁ * w₂) = P * w₂ ∧ (w₁ * w₂) * (w₁ * P) = P * w₂ := by
  constructor
  · calc (w₁ * P) * (w₁ * w₂) = w₁ * (P * w₁) * w₂ := by simp only [mul_assoc]
      _ = w₁ * (z * w₁ * P) * w₂ := by rw [hP₁]
      _ = (w₁ * z) * w₁ * P * w₂ := by simp only [mul_assoc]
      _ = (z * w₁) * w₁ * P * w₂ := by rw [hw₁z]
      _ = z * (w₁ * w₁) * P * w₂ := by simp only [mul_assoc]
      _ = z * z * P * w₂ := by rw [hw₁]
      _ = P * w₂ := by rw [hz, one_mul]
  · calc (w₁ * w₂) * (w₁ * P) = w₁ * (w₂ * w₁) * P := by simp only [mul_assoc]
      _ = w₁ * (w₁ * w₂) * P := by rw [hw]
      _ = (w₁ * w₁) * w₂ * P := by simp only [mul_assoc]
      _ = z * w₂ * P := by rw [hw₁]
      _ = P * w₂ := hP₂.symm

theorem zpow_eq_one_or_self {t : G} (ht : t * t = 1) (i : ℤ) : t ^ i = 1 ∨ t ^ i = t := by
  rcases Int.even_or_odd' i with ⟨r, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ht, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, ht, one_zpow, one_mul]

theorem comm_of_comm_mul_right {c a P : G} (hP : c * P = P * c)
    (h : c * (a * P) = (a * P) * c) : c * a = a * c := by
  apply mul_right_cancel (b := P)
  calc c * a * P = c * (a * P) := by rw [mul_assoc]
    _ = (a * P) * c := h
    _ = a * (P * c) := by rw [mul_assoc]
    _ = a * (c * P) := by rw [hP]
    _ = a * c * P := by rw [mul_assoc]

theorem comm_of_comm_mul_left {c P a : G} (hP : c * P = P * c)
    (h : c * (P * a) = (P * a) * c) : c * a = a * c := by
  apply mul_left_cancel (a := P)
  calc P * (c * a) = (P * c) * a := by rw [mul_assoc]
    _ = (c * P) * a := by rw [hP]
    _ = c * (P * a) := by rw [mul_assoc]
    _ = (P * a) * c := h
    _ = P * (a * c) := by rw [mul_assoc]

theorem conj_mul_of_sq {y a b : G} (hy : y * y = 1) :
    y * (a * b) * y = (y * a * y) * (y * b * y) := by
  calc y * (a * b) * y = y * a * 1 * b * y := by simp only [mul_one, mul_assoc]
    _ = y * a * (y * y) * b * y := by rw [hy]
    _ = (y * a * y) * (y * b * y) := by simp only [mul_assoc]

theorem conj_inv_of_sq {y a : G} (hy : y * y = 1) : y * a⁻¹ * y = (y * a * y)⁻¹ := by
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc y * a⁻¹ * y = y⁻¹ * a⁻¹ * y⁻¹ := by rw [hy']
    _ = (y * a * y)⁻¹ := by group

theorem conj_zpow_inv {y c : G} (hy : y * y = 1) (hc : y * c * y = c⁻¹) (i : ℤ) :
    y * c ^ i * y = (c ^ i)⁻¹ := by
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have := conj_zpow (a := y) (b := c) (i := i)
  rw [hy'] at this
  rw [← this, hc, inv_zpow]

theorem conj_pow_inv {y c : G} (hy : y * y = 1) (hc : y * c * y = c⁻¹) (s : ℕ) :
    y * c ^ s * y = (c ^ s)⁻¹ := by
  have := conj_zpow_inv hy hc (s : ℤ)
  simpa using this

theorem h_y_aux {h w₁ w₂ e₁ e₂ : G} (hh : h * h = e₁ * e₂) (h₁ : h * w₁ = e₁ * w₁ * h)
    (h₂ : h * w₂ = e₂ * w₂ * h) (he : w₁ * e₂ = e₂ * w₁) :
    h * (w₁ * w₂) = (h * h) * (w₁ * w₂) * h := by
  calc h * (w₁ * w₂) = (h * w₁) * w₂ := by rw [mul_assoc]
    _ = e₁ * w₁ * h * w₂ := by rw [h₁]
    _ = e₁ * w₁ * (h * w₂) := by simp only [mul_assoc]
    _ = e₁ * w₁ * (e₂ * w₂ * h) := by rw [h₂]
    _ = e₁ * (w₁ * e₂) * w₂ * h := by simp only [mul_assoc]
    _ = e₁ * (e₂ * w₁) * w₂ * h := by rw [he]
    _ = (e₁ * e₂) * (w₁ * w₂) * h := by simp only [mul_assoc]
    _ = (h * h) * (w₁ * w₂) * h := by rw [hh]

theorem y_h_aux {h y : G} (hy : y * y = 1) (hhy : h * y = (h * h) * y * h) :
    y * h * y = h⁻¹ := by
  have h1 : y = h * y * h := by
    apply mul_left_cancel (a := h)
    calc h * y = (h * h) * y * h := hhy
      _ = h * (h * y * h) := by simp only [mul_assoc]
  have h2 : y * h = h⁻¹ * y := by
    calc y * h = h⁻¹ * (h * y * h) := by group
      _ = h⁻¹ * y := by rw [← h1]
  calc y * h * y = h⁻¹ * y * y := by rw [h2]
    _ = h⁻¹ := by rw [mul_assoc, hy, mul_one]

theorem y_conj_aux {w₁ w₂ c : G} (hy : (w₁ * w₂) * (w₁ * w₂) = 1) (hc : w₁ * c * w₁⁻¹ = c⁻¹)
    (hcw : c * w₂ = w₂ * c) : (w₁ * w₂) * c * (w₁ * w₂) = c⁻¹ := by
  have hy' : (w₁ * w₂)⁻¹ = w₁ * w₂ := inv_eq_of_mul_eq_one_right hy
  have h1 : w₂ * c * w₂⁻¹ = c := by rw [← hcw, mul_assoc, mul_inv_cancel, mul_one]
  calc (w₁ * w₂) * c * (w₁ * w₂) = (w₁ * w₂) * c * (w₁ * w₂)⁻¹ := by rw [hy']
    _ = w₁ * (w₂ * c * w₂⁻¹) * w₁⁻¹ := by group
    _ = c⁻¹ := by rw [h1, hc]

end Generic

end QPShape

section QP

open QPShape

variable {G : Type*} [Group G] {n s₁ s₂ : ℕ} {c₁ c₂ w₁ w₂ h : G}

namespace QPData

theorem z_mul_z (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    c₁ ^ 2 ^ (n - 1) * c₁ ^ 2 ^ (n - 1) = 1 := by
  rw [← pow_add, ← (two_pow_aux H.two_le).1]
  exact H.c₁_pow

theorem orderOf_c₁ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : orderOf c₁ = 2 ^ n := by
  have hn1 : n - 1 + 1 = n := by have := H.two_le; omega
  have := orderOf_eq_prime_pow (p := 2) (x := c₁) H.z_ne_one (by rw [hn1]; exact H.c₁_pow)
  rwa [hn1] at this

theorem orderOf_c₂ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : orderOf c₂ = 2 ^ n := by
  have hn1 : n - 1 + 1 = n := by have := H.two_le; omega
  have := orderOf_eq_prime_pow (p := 2) (x := c₂) (by rw [H.z_eq]; exact H.z_ne_one)
    (by rw [hn1]; exact H.c₂_pow)
  rwa [hn1] at this

theorem orderOf_e₁ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : orderOf (c₁ ^ s₁) = 2 ^ n := by
  have hc : (orderOf c₁).Coprime s₁ := by
    rw [H.orderOf_c₁]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr H.s₁_odd)
  rw [Nat.Coprime.orderOf_pow hc, H.orderOf_c₁]

theorem orderOf_e₂ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : orderOf (c₂ ^ s₂) = 2 ^ n := by
  have hc : (orderOf c₂).Coprime s₂ := by
    rw [H.orderOf_c₂]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr H.s₂_odd)
  rw [Nat.Coprime.orderOf_pow hc, H.orderOf_c₂]

theorem e₁_pow_k (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    (c₁ ^ s₁) ^ 2 ^ (n - 1) = c₁ ^ 2 ^ (n - 1) := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact pow_odd_of_mul_self_eq_one H.z_mul_z H.s₁_odd

theorem e₂_pow_k (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    (c₂ ^ s₂) ^ 2 ^ (n - 1) = c₁ ^ 2 ^ (n - 1) := by
  rw [← pow_mul, mul_comm, pow_mul, H.z_eq]
  exact pow_odd_of_mul_self_eq_one H.z_mul_z H.s₂_odd

theorem c₁_mul_c₁_ne_one (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : c₁ * c₁ ≠ 1 := by
  intro h1
  apply H.z_ne_one
  exact pow_eq_one_of_mul_self_eq_one h1 ⟨2 ^ (n - 2), (two_pow_aux H.two_le).2⟩

theorem c₂_mul_c₂_ne_one (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : c₂ * c₂ ≠ 1 := by
  intro h1
  apply H.z_ne_one
  rw [← H.z_eq]
  exact pow_eq_one_of_mul_self_eq_one h1 ⟨2 ^ (n - 2), (two_pow_aux H.two_le).2⟩

theorem h_pow_two_pow_n (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : h ^ 2 ^ n = 1 := by
  have hc : Commute (c₁ ^ s₁) (c₂ ^ s₂) := (Commute.pow_pow H.c₁_c₂ s₁ s₂)
  rw [(two_pow_aux H.two_le).1, ← two_mul, pow_mul, sq, H.h_sq, hc.mul_pow, H.e₁_pow_k,
    H.e₂_pow_k]
  exact H.z_mul_z

theorem h_pow_k_ne_one (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : h ^ 2 ^ (n - 1) ≠ 1 := by
  intro h1
  obtain ⟨-, hkj⟩ := two_pow_aux H.two_le
  have hc : Commute (c₁ ^ s₁) (c₂ ^ s₂) := (Commute.pow_pow H.c₁_c₂ s₁ s₂)
  have hh : h ^ 2 ^ (n - 1) = (c₁ ^ s₁) ^ 2 ^ (n - 2) * (c₂ ^ s₂) ^ 2 ^ (n - 2) := by
    rw [hkj, ← two_mul, pow_mul, sq, H.h_sq, hc.mul_pow]
  have hmem : (c₁ ^ s₁) ^ 2 ^ (n - 2) ∈ zpowers (c₁ ^ 2 ^ (n - 1)) := by
    apply H.inter
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact pow_mem (pow_mem (mem_zpowers c₁) _) _
    · have : (c₁ ^ s₁) ^ 2 ^ (n - 2) = ((c₂ ^ s₂) ^ 2 ^ (n - 2))⁻¹ :=
        eq_inv_of_mul_eq_one_left (hh ▸ h1)
      rw [this]
      exact inv_mem (pow_mem (pow_mem (mem_zpowers c₂) _) _)
  have hsq := mul_self_eq_one_of_mem_zpowers H.z_mul_z hmem
  rw [← pow_add, ← hkj, H.e₁_pow_k] at hsq
  exact H.z_ne_one hsq

theorem orderOf_h (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : orderOf h = 2 ^ n := by
  have hn1 : n - 1 + 1 = n := by have := H.two_le; omega
  have := orderOf_eq_prime_pow (p := 2) (x := h) H.h_pow_k_ne_one
    (by rw [hn1]; exact H.h_pow_two_pow_n)
  rwa [hn1] at this

theorem commute_h_c₁ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : Commute h c₁ := H.h_c₁

theorem commute_h_c₂ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : Commute h c₂ := H.h_c₂

theorem commute_c₁_c₂ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : Commute c₁ c₂ := H.c₁_c₂

theorem commute_c₁_w₂ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : Commute c₁ w₂ := H.c₁_w₂

theorem commute_w₁_c₂ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : Commute w₁ c₂ := H.w₁_c₂

theorem h_w₁' (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : h * w₁ = c₁ ^ s₁ * w₁ * h :=
  mul_inv_eq_iff_eq_mul.mp H.h_w₁

theorem h_w₂' (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : h * w₂ = c₂ ^ s₂ * w₂ * h :=
  mul_inv_eq_iff_eq_mul.mp H.h_w₂

theorem w₁_conj' (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : w₁⁻¹ * c₁ * w₁ = c₁⁻¹ :=
  inv_conj_of_conj H.w₁_conj

theorem hk_w₁ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    h ^ 2 ^ (n - 1) * w₁ = c₁ ^ 2 ^ (n - 1) * w₁ * h ^ 2 ^ (n - 1) := by
  have := pow_mul_of_mul_eq (Commute.pow_right H.commute_h_c₁ s₁) H.h_w₁'
    (2 ^ (n - 1))
  rwa [H.e₁_pow_k] at this

theorem hk_w₂ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    h ^ 2 ^ (n - 1) * w₂ = c₁ ^ 2 ^ (n - 1) * w₂ * h ^ 2 ^ (n - 1) := by
  have := pow_mul_of_mul_eq (Commute.pow_right H.commute_h_c₂ s₂) H.h_w₂'
    (2 ^ (n - 1))
  rwa [H.e₂_pow_k] at this

theorem w₁_z (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    w₁ * c₁ ^ 2 ^ (n - 1) = c₁ ^ 2 ^ (n - 1) * w₁ := by
  rw [← H.w₁_sq]
  exact (mul_assoc w₁ w₁ w₁).symm

theorem hkhk (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : h ^ 2 ^ (n - 1) * h ^ 2 ^ (n - 1) = 1 := by
  rw [← pow_add, ← (two_pow_aux H.two_le).1]
  exact H.h_pow_two_pow_n

theorem w₁_inv_h_w₁ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    w₁⁻¹ * h * w₁ = (c₁ ^ s₁)⁻¹ * h := by
  calc w₁⁻¹ * h * w₁ = w₁⁻¹ * (h * w₁) := by rw [mul_assoc]
    _ = w₁⁻¹ * (c₁ ^ s₁ * w₁ * h) := by rw [H.h_w₁']
    _ = (w₁⁻¹ * c₁ ^ s₁ * w₁) * h := by simp only [mul_assoc]
    _ = (c₁ ^ s₁)⁻¹ * h := by rw [inv_conj_pow H.w₁_conj']

theorem at_eq (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    (qpT n w₁ h)⁻¹ * h * qpT n w₁ h = (c₁ ^ s₁)⁻¹ * h := by
  have hP : Commute (h ^ 2 ^ (n - 1)) ((c₁ ^ s₁)⁻¹ * h) :=
    Commute.mul_right (Commute.inv_right (Commute.pow_pow H.commute_h_c₁ _ s₁))
      (Commute.pow_left (Commute.refl h) _)
  unfold qpT
  rw [mul_inv_rev]
  calc (h ^ 2 ^ (n - 1))⁻¹ * w₁⁻¹ * h * (w₁ * h ^ 2 ^ (n - 1))
      = (h ^ 2 ^ (n - 1))⁻¹ * (w₁⁻¹ * h * w₁) * h ^ 2 ^ (n - 1) := by simp only [mul_assoc]
    _ = (h ^ 2 ^ (n - 1))⁻¹ * ((c₁ ^ s₁)⁻¹ * h) * h ^ 2 ^ (n - 1) := by rw [H.w₁_inv_h_w₁]
    _ = (c₁ ^ s₁)⁻¹ * h := by rw [mul_assoc, ← hP.eq, inv_mul_cancel_left]

theorem t_sq (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : qpT n w₁ h * qpT n w₁ h = 1 :=
  t_sq_aux H.z_mul_z H.w₁_z H.w₁_sq H.hk_w₁ H.hkhk

theorem ty (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    qpT n w₁ h * qpY w₁ w₂ = h ^ 2 ^ (n - 1) * w₂ ∧
      qpY w₁ w₂ * qpT n w₁ h = h ^ 2 ^ (n - 1) * w₂ :=
  ty_aux H.z_mul_z H.w₁_z H.w₁_sq H.w₁_w₂ H.hk_w₁ H.hk_w₂

theorem y_sq (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : qpY w₁ w₂ * qpY w₁ w₂ = 1 := by
  unfold qpY
  calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by simp only [mul_assoc]
    _ = w₁ * (w₁ * w₂) * w₂ := by rw [H.w₁_w₂]
    _ = (w₁ * w₁) * (w₂ * w₂) := by simp only [mul_assoc]
    _ = 1 := by rw [H.w₁_sq, H.w₂_sq]; exact H.z_mul_z

theorem t_ne_one (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : qpT n w₁ h ≠ 1 := by
  intro h1
  have hw : w₁ = (h ^ 2 ^ (n - 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
  apply not_commute_of_conj H.w₁_conj H.c₁_mul_c₁_ne_one
  rw [hw]
  exact (((H.commute_h_c₁.pow_left _).symm).inv_right)

theorem y_ne_one (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : qpY w₁ w₂ ≠ 1 := by
  intro h1
  have hw : w₁ = w₂⁻¹ := eq_inv_of_mul_eq_one_left h1
  apply not_commute_of_conj H.w₁_conj H.c₁_mul_c₁_ne_one
  rw [hw]
  exact H.commute_c₁_w₂.inv_right

theorem t_ne_y (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : qpT n w₁ h ≠ qpY w₁ w₂ := by
  intro h1
  have hw : h ^ 2 ^ (n - 1) = w₂ := mul_left_cancel h1
  apply not_commute_of_conj H.w₂_conj H.c₂_mul_c₂_ne_one
  rw [← hw]
  exact (H.commute_h_c₂.pow_left _).symm

theorem commute_h_at (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : Commute h ((c₁ ^ s₁)⁻¹ * h) :=
  (H.commute_h_c₁.pow_right s₁).inv_right.mul_right (Commute.refl h)

theorem h_zpow_two_mul (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) (r : ℤ) :
    h ^ (2 * r) = (c₁ ^ s₁) ^ r * (c₂ ^ s₂) ^ r := by
  have hc : Commute (c₁ ^ s₁) (c₂ ^ s₂) := Commute.pow_pow H.commute_c₁_c₂ s₁ s₂
  rw [zpow_mul, zpow_two, H.h_sq, hc.mul_zpow]

theorem zpow_h_eq_one_of_mem (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) {l : ℤ}
    (hl : h ^ l ∈ zpowers c₁) : h ^ l = 1 := by
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hl
  rcases Int.even_or_odd' l with ⟨r, rfl | rfl⟩
  · have h3 : (c₂ ^ s₂) ^ r = ((c₁ ^ s₁) ^ r)⁻¹ * c₁ ^ m := by
      rw [hm, H.h_zpow_two_mul, inv_mul_cancel_left]
    have hmem1 : (c₂ ^ s₂) ^ r ∈ zpowers c₁ := by
      rw [h3]
      exact mul_mem (inv_mem (zpow_mem (pow_mem (mem_zpowers c₁) s₁) r))
        (zpow_mem (mem_zpowers c₁) m)
    have hmem2 : (c₂ ^ s₂) ^ r ∈ zpowers c₂ := zpow_mem (pow_mem (mem_zpowers c₂) s₂) r
    have h4 := mul_self_eq_one_of_mem_zpowers H.z_mul_z (H.inter (mem_inf.mpr ⟨hmem1, hmem2⟩))
    rw [← zpow_add, ← orderOf_dvd_iff_zpow_eq_one, H.orderOf_e₂] at h4
    rw [← orderOf_dvd_iff_zpow_eq_one, H.orderOf_h, two_mul]
    exact h4
  · exfalso
    apply H.h_not_mem
    have hc₁ : c₁ ∈ closure ({c₁, c₂} : Set G) := subset_closure (by simp)
    have hc₂ : c₂ ∈ closure ({c₁, c₂} : Set G) := subset_closure (by simp)
    have h1 : h = (h ^ (2 * r))⁻¹ * h ^ (2 * r + 1) := by
      rw [zpow_add_one, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1, ← hm, H.h_zpow_two_mul]
    exact mul_mem (inv_mem (mul_mem (zpow_mem (pow_mem hc₁ _) _) (zpow_mem (pow_mem hc₂ _) _)))
      (zpow_mem hc₁ _)

theorem inf_bot_h_at (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    zpowers h ⊓ zpowers ((qpT n w₁ h)⁻¹ * h * qpT n w₁ h) = ⊥ := by
  rw [H.at_eq, eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx1
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hx2
  have hc : Commute ((c₁ ^ s₁)⁻¹) h := (H.commute_h_c₁.pow_right s₁).inv_right.symm
  rw [hc.mul_zpow, inv_zpow] at hj
  have h1 : h ^ (i - j) = ((c₁ ^ s₁) ^ j)⁻¹ := by
    rw [zpow_sub, ← hj, mul_inv_cancel_right]
  have h2 : (c₁ ^ s₁) ^ j = 1 := by
    have hmem : h ^ (i - j) ∈ zpowers c₁ := by
      rw [h1]
      exact inv_mem (zpow_mem (pow_mem (mem_zpowers c₁) s₁) j)
    have := H.zpow_h_eq_one_of_mem hmem
    rw [h1, inv_eq_one] at this
    exact this
  have h3 : h ^ j = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, H.orderOf_h, ← H.orderOf_e₁,
      orderOf_dvd_iff_zpow_eq_one]
    exact h2
  rw [h2, h3, inv_one, one_mul] at hj
  rw [Subgroup.mem_bot]
  exact hj.symm

theorem y_h (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : qpY w₁ w₂ * h * qpY w₁ w₂ = h⁻¹ := by
  have hhe : w₁ * c₂ ^ s₂ = c₂ ^ s₂ * w₁ := (H.commute_w₁_c₂.pow_right s₂).eq
  exact y_h_aux H.y_sq (h_y_aux H.h_sq H.h_w₁' H.h_w₂' hhe)

theorem y_c₁ (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) : qpY w₁ w₂ * c₁ * qpY w₁ w₂ = c₁⁻¹ :=
  y_conj_aux H.y_sq H.w₁_conj H.c₁_w₂

theorem y_inv (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    ∀ x ∈ qpA n w₁ h, qpY w₁ w₂ * x * qpY w₁ w₂ = x⁻¹ := by
  intro x hx
  unfold qpA at hx
  rw [H.at_eq] at hx
  obtain ⟨i, j, rfl⟩ := (mem_zpowers_sup_iff H.commute_h_at).mp hx
  have hye : qpY w₁ w₂ * c₁ ^ s₁ * qpY w₁ w₂ = (c₁ ^ s₁)⁻¹ := conj_pow_inv H.y_sq H.y_c₁ s₁
  have hyei : qpY w₁ w₂ * (c₁ ^ s₁)⁻¹ * qpY w₁ w₂ = c₁ ^ s₁ := by
    rw [conj_inv_of_sq H.y_sq, hye, inv_inv]
  have hyu : qpY w₁ w₂ * ((c₁ ^ s₁)⁻¹ * h) * qpY w₁ w₂ = ((c₁ ^ s₁)⁻¹ * h)⁻¹ := by
    rw [conj_mul_of_sq H.y_sq, hyei, H.y_h, mul_inv_rev, inv_inv]
    exact (H.commute_h_c₁.pow_right s₁).inv_left.eq.symm
  have hyh : qpY w₁ w₂ * h ^ i * qpY w₁ w₂ = (h ^ i)⁻¹ := conj_zpow_inv H.y_sq H.y_h i
  have hyuj : qpY w₁ w₂ * ((c₁ ^ s₁)⁻¹ * h) ^ j * qpY w₁ w₂ = (((c₁ ^ s₁)⁻¹ * h) ^ j)⁻¹ :=
    conj_zpow_inv H.y_sq hyu j
  rw [conj_mul_of_sq H.y_sq, hyh, hyuj, mul_inv_rev]
  exact ((H.commute_h_at.zpow_zpow i j).inv_left.inv_right).eq

theorem A_le_centralizer (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    qpA n w₁ h ≤ centralizer ({c₁, c₂} : Set G) := by
  unfold qpA
  rw [H.at_eq]
  refine sup_le ?_ ?_
  · rw [zpowers_le, mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | hg
    · exact H.commute_h_c₁.symm.eq
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact H.commute_h_c₂.symm.eq
  · rw [zpowers_le, mem_centralizer_iff]
    intro g hg
    rcases hg with rfl | hg
    · exact ((Commute.refl g).pow_right s₁).inv_right.mul_right H.commute_h_c₁.symm |>.eq
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact ((H.commute_c₁_c₂.symm.pow_right s₁).inv_right.mul_right H.commute_h_c₂.symm).eq

theorem commute_t_y (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    Commute (qpT n w₁ h) (qpY w₁ w₂) :=
  H.ty.1.trans H.ty.2.symm

theorem t_not_comm (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    ¬ (c₁ * qpT n w₁ h = qpT n w₁ h * c₁) := by
  intro hc
  unfold qpT at hc
  apply not_commute_of_conj H.w₁_conj H.c₁_mul_c₁_ne_one
  exact comm_of_comm_mul_right (H.commute_h_c₁.pow_left _).symm.eq hc

theorem y_not_comm (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    ¬ (c₁ * qpY w₁ w₂ = qpY w₁ w₂ * c₁) := by
  intro hc
  unfold qpY at hc
  apply not_commute_of_conj H.w₁_conj H.c₁_mul_c₁_ne_one
  exact comm_of_comm_mul_right H.c₁_w₂ hc

theorem ty_not_comm (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    ¬ (c₂ * (h ^ 2 ^ (n - 1) * w₂) = (h ^ 2 ^ (n - 1) * w₂) * c₂) := by
  intro hc
  apply not_commute_of_conj H.w₂_conj H.c₂_mul_c₂_ne_one
  exact comm_of_comm_mul_left (H.commute_h_c₂.pow_left _).symm.eq hc

theorem A_inf_bot (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    qpA n w₁ h ⊓ (zpowers (qpT n w₁ h) ⊔ zpowers (qpY w₁ w₂)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxV⟩ := mem_inf.mp hx
  have hcen := mem_centralizer_iff.mp (H.A_le_centralizer hxA)
  have hc₁ : c₁ * x = x * c₁ := hcen c₁ (by simp)
  have hc₂ : c₂ * x = x * c₂ := hcen c₂ (by simp)
  obtain ⟨i, j, rfl⟩ := (mem_zpowers_sup_iff H.commute_t_y).mp hxV
  rw [Subgroup.mem_bot]
  rcases zpow_eq_one_or_self H.t_sq i with hi | hi <;>
    rcases zpow_eq_one_or_self H.y_sq j with hj | hj
  · rw [hi, hj, one_mul]
  · exfalso
    rw [hi, hj, one_mul] at hc₁
    exact H.y_not_comm hc₁
  · exfalso
    rw [hi, hj, mul_one] at hc₁
    exact H.t_not_comm hc₁
  · exfalso
    rw [hi, hj, H.ty.1] at hc₂
    exact H.ty_not_comm hc₂

end QPData

theorem shapeConds_of_qpData (H : QPData n s₁ s₂ c₁ c₂ w₁ w₂ h) :
    ShapeConds (qpS n w₁ w₂ h) (qpA n w₁ h) h (qpT n w₁ h) (qpY w₁ w₂) n := by
  unfold ShapeConds
  refine ⟨H.orderOf_h, rfl, H.inf_bot_h_at, ?_, H.t_sq, H.y_sq, H.commute_t_y, H.t_ne_one,
    H.y_ne_one, H.t_ne_y, H.A_inf_bot, H.y_inv, rfl⟩
  rw [H.at_eq]
  exact H.commute_h_at.eq

end QP

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
