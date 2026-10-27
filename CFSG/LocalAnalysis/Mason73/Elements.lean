module

import Mathlib.Tactic.LinearCombination
public import CFSG.LocalAnalysis.Mason73.Coord

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

abbrev hh (n : ℕ) : ZMod (2 ^ n) := ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))

theorem two_mul_hh (hn : 1 ≤ n) : 2 * hh n = 0 := by
  rw [hh, show (2 : ZMod (2 ^ n)) = ((2 : ℕ) : ZMod (2 ^ n)) by norm_num, ← Nat.cast_mul,
    ← pow_succ', show n - 1 + 1 = n by omega, ZMod.natCast_self]

theorem hh_add_hh (hn : 1 ≤ n) : hh n + hh n = 0 := by
  rw [← two_mul, two_mul_hh hn]

theorem neg_hh (hn : 1 ≤ n) : -hh n = hh n := by
  rw [neg_eq_iff_add_eq_zero, hh_add_hh hn]

theorem hh_mul_natCast_eq_iff (hn : 1 ≤ n) (a b : ℕ) :
    hh n * (a : ZMod (2 ^ n)) = hh n * (b : ZMod (2 ^ n)) ↔ a % 2 = b % 2 := by
  have key : ∀ c : ℕ, hh n * (c : ZMod (2 ^ n)) = hh n * ((c % 2 : ℕ) : ZMod (2 ^ n)) := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c 2]
    rw [Nat.cast_add, mul_add, Nat.cast_mul, Nat.cast_two, ← mul_assoc, mul_comm (hh n) 2,
      two_mul_hh hn, zero_mul, add_zero]
  have hval : ∀ c : ℕ, hh n * (c : ZMod (2 ^ n)) = ((2 ^ (n - 1) * c : ℕ) : ZMod (2 ^ n)) := by
    intro c
    rw [hh, Nat.cast_mul]
  have hlt : ∀ c : ℕ, c < 2 → 2 ^ (n - 1) * c < 2 ^ n := by
    intro c hc
    calc 2 ^ (n - 1) * c < 2 ^ (n - 1) * 2 := Nat.mul_lt_mul_of_pos_left hc (by positivity)
      _ = 2 ^ n := by rw [← pow_succ]; congr 1; omega
  constructor
  · intro h
    rw [key a, key b, hval, hval] at h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (hlt _ (Nat.mod_lt _ (by norm_num))),
      ZMod.val_natCast_of_lt (hlt _ (Nat.mod_lt _ (by norm_num)))] at h'
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  · intro h
    rw [key a, key b, h]

@[expose] def hv (n : ℕ) (χ : Fin 4 → ℕ) : Fin 4 → ZMod (2 ^ n) :=
  fun i => hh n * (χ i : ZMod (2 ^ n))

theorem hv_sub_hv_isConst_iff (hn : 1 ≤ n) (χ χ' : Fin 4 → ℕ) :
    IsConst (hv n χ - hv n χ') ↔ ∀ i j, (χ i + χ' j) % 2 = (χ j + χ' i) % 2 := by
  constructor
  · intro h i j
    have h1 := h i j
    simp only [hv, Pi.sub_apply] at h1
    have h2 : hh n * ((χ i + χ' j : ℕ) : ZMod (2 ^ n)) =
        hh n * ((χ j + χ' i : ℕ) : ZMod (2 ^ n)) := by
      rw [Nat.cast_add, Nat.cast_add, mul_add, mul_add]
      linear_combination h1
    exact (hh_mul_natCast_eq_iff hn _ _).1 h2
  · intro h i j
    have h2 := (hh_mul_natCast_eq_iff hn _ _).2 (h i j)
    rw [Nat.cast_add, Nat.cast_add, mul_add, mul_add] at h2
    simp only [hv, Pi.sub_apply]
    linear_combination h2

theorem pv_hv (π : Perm (Fin 4)) (χ : Fin 4 → ℕ) :
    pv π (hv n χ) = hv n (fun i => χ (π⁻¹ i)) := rfl

theorem sum_hv_four (χ : Fin 4 → ℕ) :
    ∑ i, hv n χ i = hh n * ((χ 0 + χ 1 + χ 2 + χ 3 : ℕ) : ZMod (2 ^ n)) := by
  simp only [hv, Fin.sum_univ_four]
  push_cast
  ring

theorem detSum_hv (hn : 1 ≤ n) {χ : Fin 4 → ℕ} (hχ : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 0) :
    detSum (hv n χ) 1 := by
  rw [detSum_one_iff, sum_hv_four]
  have := (hh_mul_natCast_eq_iff hn (χ 0 + χ 1 + χ 2 + χ 3) 0).2 (by simpa using hχ)
  rw [this, Nat.cast_zero, mul_zero]

theorem el_hv_eq_el_hv_iff (hn : 2 ≤ n) {χ χ' : Fin 4 → ℕ} (h : detSum (hv n χ) 1)
    (h' : detSum (hv n χ') 1) :
    el (hv n χ) 1 h = el (hv n χ') 1 h' ↔ ∀ i j, (χ' i + χ j) % 2 = (χ' j + χ i) % 2 := by
  rw [el_eq_el_iff hn, hv_sub_hv_isConst_iff (by omega)]
  simp

abbrev χz : Fin 4 → ℕ := ![1, 1, 0, 0]
abbrev χx1 : Fin 4 → ℕ := ![1, 0, 1, 0]
abbrev χy1 : Fin 4 → ℕ := ![1, 0, 0, 1]

@[expose] def zT (hn : 1 ≤ n) : L4Model n := el (hv n χz) 1 (detSum_hv hn (by decide))

@[expose] def x1T (hn : 1 ≤ n) : L4Model n := el (hv n χx1) 1 (detSum_hv hn (by decide))

@[expose] def y1T (hn : 1 ≤ n) : L4Model n := el (hv n χy1) 1 (detSum_hv hn (by decide))

theorem hv_add (χ χ' : Fin 4 → ℕ) : hv n χ + hv n χ' = hv n (χ + χ') := by
  funext i
  simp only [hv, Pi.add_apply, Nat.cast_add]
  ring

theorem x1T_mul_y1T (hn : 2 ≤ n) : x1T (n := n) (by omega) * y1T (by omega) = zT (by omega) := by
  rw [x1T, y1T, zT, el_mul]
  simp only [mul_one, OneMemClass.coe_one, pv_one, hv_add]
  rw [el_hv_eq_el_hv_iff hn]
  decide

theorem mem_A_of_one {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) : el d 1 h ∈ A n :=
  (el_mem_A h).2 rfl

theorem zT_mem_A (hn : 1 ≤ n) : zT (n := n) hn ∈ A n := mem_A_of_one _
theorem x1T_mem_A (hn : 1 ≤ n) : x1T (n := n) hn ∈ A n := mem_A_of_one _
theorem y1T_mem_A (hn : 1 ≤ n) : y1T (n := n) hn ∈ A n := mem_A_of_one _

theorem el_hv_ne_one (hn : 2 ≤ n) {χ : Fin 4 → ℕ} (h : detSum (hv n χ) 1)
    (hχ : ∃ i j, χ i % 2 ≠ χ j % 2) : el (hv n χ) 1 h ≠ 1 := by
  rw [← el_zero_one]
  intro heq
  have h0 : (0 : Fin 4 → ZMod (2 ^ n)) = hv n (fun _ => 0) := by
    funext i
    simp [hv]
  rw [el_eq_el_iff hn] at heq
  obtain ⟨i, j, hij⟩ := hχ
  have h1 := heq.2 i j
  simp only [Pi.sub_apply, Pi.zero_apply, zero_sub, neg_inj] at h1
  have h2 := (hh_mul_natCast_eq_iff (by omega) (χ i) (χ j)).1 h1
  exact hij h2

theorem el_hv_sq (hn : 2 ≤ n) {χ : Fin 4 → ℕ} (h : detSum (hv n χ) 1) :
    el (hv n χ) 1 h * el (hv n χ) 1 h = 1 := by
  rw [el_mul, ← el_zero_one, el_eq_el_iff hn]
  refine ⟨mul_one 1, fun i j => ?_⟩
  simp only [OneMemClass.coe_one, pv_one, Pi.sub_apply, Pi.zero_apply, Pi.add_apply, hv,
    zero_sub, neg_inj]
  rw [← mul_add, ← mul_add, ← Nat.cast_add, ← Nat.cast_add, hh_mul_natCast_eq_iff (by omega)]
  omega

theorem orderOf_el_hv (hn : 2 ≤ n) {χ : Fin 4 → ℕ} (h : detSum (hv n χ) 1)
    (hχ : ∃ i j, χ i % 2 ≠ χ j % 2) : orderOf (el (hv n χ) 1 h) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact el_hv_sq hn h) (el_hv_ne_one hn h hχ)

theorem orderOf_zT (hn : 2 ≤ n) : orderOf (zT (n := n) (by omega)) = 2 :=
  orderOf_el_hv hn _ ⟨0, 2, by decide⟩

theorem orderOf_x1T (hn : 2 ≤ n) : orderOf (x1T (n := n) (by omega)) = 2 :=
  orderOf_el_hv hn _ ⟨0, 1, by decide⟩

theorem orderOf_y1T (hn : 2 ≤ n) : orderOf (y1T (n := n) (by omega)) = 2 :=
  orderOf_el_hv hn _ ⟨0, 1, by decide⟩

theorem χz_pv_const : ∀ π : Perm (Fin 4), π ∈ Fin81.R0 → ∀ i j : Fin 4,
    (χz i + χz (π⁻¹ j)) % 2 = (χz j + χz (π⁻¹ i)) % 2 := by
  decide

theorem zT_mem_center (hn : 2 ≤ n) : zT (n := n) (by omega) ∈ Subgroup.center (L4Model n) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [zT, el_mul, el_mul, el_eq_el_iff hn]
  refine ⟨by rw [mul_one, one_mul], ?_⟩
  simp only [OneMemClass.coe_one, pv_one]
  have hconst := (hv_sub_hv_isConst_iff (n := n) (by omega) χz
    (fun i => χz ((π : Perm (Fin 4))⁻¹ i))).2 (fun i j => χz_pv_const _ π.2 i j)
  intro i j
  have h1 := hconst i j
  simp only [Pi.sub_apply] at h1
  simp only [Pi.sub_apply, Pi.add_apply, pv_hv] at h1 ⊢
  linear_combination h1

end CFSG.LocalAnalysis.Mason73
