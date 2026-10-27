module

public import CFSG.LocalAnalysis.Mason73.Quaternion
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

theorem el_congr {d d' : Fin 4 → ZMod (2 ^ n)} {π π' : Fin81.R0} (h : detSum d π)
    (h' : detSum d' π') (hd : d = d') (hπ : π = π') : el d π h = el d' π' h' := by
  subst hd hπ
  rfl

theorem detSum_pv {e : Fin 4 → ZMod (2 ^ n)} (π : Perm (Fin 4)) (h : detSum e 1) :
    detSum (pv π e) 1 := by
  rw [detSum_one_iff] at h ⊢
  rw [sum_pv, h]

theorem el_conj (hn : 2 ≤ n) {d e : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π)
    (h' : detSum e 1) :
    el d π h * el e 1 h' * (el d π h)⁻¹ = el (pv (π : Perm (Fin 4)) e) 1 (detSum_pv _ h') := by
  rw [mul_inv_eq_iff_eq_mul, el_mul, el_mul, el_eq_el_iff hn]
  refine ⟨by rw [mul_one, one_mul], fun i j => ?_⟩
  simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one]
  ring

theorem exists_hh_of_two_mul (hn : 1 ≤ n) {x : ZMod (2 ^ n)} (hx : 2 * x = 0) :
    ∃ b : ℕ, b < 2 ∧ x = hh n * (b : ZMod (2 ^ n)) := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  have hx' : ((2 * x.val : ℕ) : ZMod (2 ^ n)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact_mod_cast hx
  have hlt := ZMod.val_lt x
  rcases mod_eq_of_two_mul_zero hn hx' with h | h <;> rw [Nat.mod_eq_of_lt hlt] at h
  · refine ⟨0, by norm_num, ?_⟩
    rw [← ZMod.natCast_zmod_val x, h]
    simp
  · refine ⟨1, by norm_num, ?_⟩
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_one, mul_one]

theorem exists_hv_of_two_mul (hn : 1 ≤ n) {e : Fin 4 → ZMod (2 ^ n)} (he : ∀ i, 2 * e i = 0) :
    ∃ χ : Fin 4 → ℕ, (∀ i, χ i < 2) ∧ e = hv n χ := by
  choose χ hχ he' using fun i => exists_hh_of_two_mul hn (he i)
  exact ⟨χ, hχ, funext he'⟩

abbrev ss (n : ℕ) : ZMod (2 ^ n) := ((2 ^ (n - 3) : ℕ) : ZMod (2 ^ n))

theorem four_mul_ss (hn : 3 ≤ n) : 4 * ss n = hh n := by
  rw [ss, hh, show (4 : ZMod (2 ^ n)) = ((4 : ℕ) : ZMod (2 ^ n)) by norm_num, ← Nat.cast_mul]
  congr 1
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

@[expose] def wv (n : ℕ) (χ : Fin 4 → ℕ) : Fin 4 → ZMod (2 ^ n) := fun i => ss n + hv n χ i

theorem detSum_wv (hn : 3 ≤ n) {χ : Fin 4 → ℕ} (hχ : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 1) :
    detSum (wv n χ) 1 := by
  rw [detSum_one_iff]
  have h1 : ∑ i, wv n χ i = 4 * ss n + ∑ i, hv n χ i := by
    simp only [wv, Fin.sum_univ_four]
    ring
  rw [h1, sum_hv_four, four_mul_ss hn,
    (hh_mul_natCast_eq_iff (by omega) (χ 0 + χ 1 + χ 2 + χ 3) 1).2 (by omega), Nat.cast_one,
    mul_one, hh_add_hh (by omega)]

theorem eq_of_mem_A_of_mul_self (hn : 3 ≤ n) {a : L4Model n} (ha : a ∈ A n) (ha2 : a * a = 1) :
    ∃ χ : Fin 4 → ℕ, (∀ i, χ i < 2) ∧ χ 0 = 0 ∧
      ((∃ h : detSum (hv n χ) 1, (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 0 ∧ a = el (hv n χ) 1 h) ∨
        (∃ h : detSum (wv n χ) 1, (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 1 ∧ a = el (wv n χ) 1 h)) := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el a
  rw [el_mem_A] at ha
  subst ha
  rw [el_mul, ← el_zero_one, el_eq_el_iff (by omega)] at ha2
  have h2 : ∀ i, 2 * (d i - d 0) = 0 := by
    intro i
    have h1 := ha2.2 i 0
    simp only [Pi.sub_apply, Pi.zero_apply, Pi.add_apply, OneMemClass.coe_one, pv_one,
      zero_sub, neg_inj] at h1
    linear_combination h1
  obtain ⟨χ, hχ2, hχ⟩ := exists_hv_of_two_mul (e := fun i => d i - d 0) (by omega) h2
  have he : ∀ i, d i - d 0 = hv n χ i := fun i => congrFun hχ i
  have hχ0 : χ 0 = 0 := by
    have h0 := he 0
    rw [sub_self] at h0
    have := (hh_mul_natCast_eq_iff (n := n) (by omega) (χ 0) 0).1
      (by rw [Nat.cast_zero, mul_zero]; exact h0.symm)
    have := hχ2 0
    omega
  refine ⟨χ, hχ2, hχ0, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one (χ 0 + χ 1 + χ 2 + χ 3) with hpar | hpar
  · refine Or.inl ⟨detSum_hv (by omega) hpar, hpar, ?_⟩
    rw [el_eq_el_iff (by omega)]
    refine ⟨rfl, fun i j => ?_⟩
    simp only [Pi.sub_apply]
    linear_combination he j - he i
  · refine Or.inr ⟨detSum_wv hn hpar, hpar, ?_⟩
    rw [el_eq_el_iff (by omega)]
    refine ⟨rfl, fun i j => ?_⟩
    simp only [Pi.sub_apply, wv]
    linear_combination he j - he i

theorem pow_two_pow_pred_of_mem_A (hn : 2 ≤ n) {a : L4Model n} (ha : a ∈ A n) :
    ∃ χ : Fin 4 → ℕ, ∃ hpar : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 0,
      a ^ 2 ^ (n - 1) = el (hv n χ) 1 (detSum_hv (by omega) hpar) := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el a
  rw [el_mem_A] at ha
  subst ha
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  have hpar : ((d 0).val + (d 1).val + (d 2).val + (d 3).val) % 2 = 0 := by
    have hs := detSum_one_iff.1 hd
    rw [Fin.sum_univ_four] at hs
    have h0 : (((d 0).val + (d 1).val + (d 2).val + (d 3).val : ℕ) : ZMod (2 ^ n)) = 0 := by
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id', id]
      exact hs
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact Nat.mod_eq_zero_of_dvd ((dvd_pow_self 2 (by omega : n ≠ 0)).trans h0)
  refine ⟨fun i => (d i).val, hpar, ?_⟩
  rw [el_one_pow]
  apply el_congr _ _ _ rfl
  funext i
  simp only [Pi.smul_apply, nsmul_eq_mul, hv, ZMod.natCast_zmod_val]

theorem el_wv_ne_el_hv (hn : 3 ≤ n) {χ χ' : Fin 4 → ℕ} (hχ : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 1)
    (hχ' : (χ' 0 + χ' 1 + χ' 2 + χ' 3) % 2 = 0) (h : detSum (wv n χ) 1)
    (h' : detSum (hv n χ') 1) : el (wv n χ) 1 h ≠ el (hv n χ') 1 h' := by
  intro heq
  rw [el_eq_el_iff (by omega)] at heq
  have key : ∀ i j, (χ' i + χ j) % 2 = (χ' j + χ i) % 2 := by
    intro i j
    have h1 := heq.2 i j
    simp only [Pi.sub_apply, wv, hv] at h1
    apply (hh_mul_natCast_eq_iff (n := n) (by omega) _ _).1
    rw [Nat.cast_add, Nat.cast_add]
    linear_combination h1
  have := key 1 0
  have := key 2 0
  have := key 3 0
  omega

theorem el_wv_ne_pow_of_mem_A (hn : 3 ≤ n) {χ : Fin 4 → ℕ}
    (hχ : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 1) (h : detSum (wv n χ) 1) {a : L4Model n}
    (ha : a ∈ A n) : a ^ 2 ^ (n - 1) ≠ el (wv n χ) 1 h := by
  obtain ⟨χ', hχ', heq⟩ := pow_two_pow_pred_of_mem_A (by omega) ha
  rw [heq]
  exact (el_wv_ne_el_hv hn hχ hχ' h _).symm

@[expose] def w1T (hn : 3 ≤ n) : L4Model n := el (wv n ![1, 0, 0, 0]) 1 (detSum_wv hn (by decide))

theorem w1T_mem_A (hn : 3 ≤ n) : w1T (n := n) hn ∈ A n := mem_A_of_one _

theorem pow_ne_w1T (hn : 3 ≤ n) {a : L4Model n} (ha : a ∈ A n) : a ^ 2 ^ (n - 1) ≠ w1T hn :=
  el_wv_ne_pow_of_mem_A hn (by decide) _ ha

@[expose] def xT (n : ℕ) : L4Model n :=
  el ![1, 0, -1, 0] 1 (by rw [detSum_one_iff, Fin.sum_univ_four]; simp)

theorem xT_mem_A : xT n ∈ A n := mem_A_of_one _

theorem el_iv_pow (hn : 1 ≤ n) {κ : Fin 4 → ℤ} {χ : Fin 4 → ℕ} (hκχ : ∀ i, (κ i - χ i) % 2 = 0)
    (h : detSum (iv n κ) 1) (h' : detSum (hv n χ) 1) :
    el (iv n κ) 1 h ^ 2 ^ (n - 1) = el (hv n χ) 1 h' := by
  rw [el_one_pow]
  apply el_congr _ _ _ rfl
  funext i
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (hκχ i)
  have hκ : κ i = χ i + 2 * k := by omega
  simp only [Pi.smul_apply, nsmul_eq_mul, hv, iv]
  rw [hκ, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_two]
  linear_combination (k : ZMod (2 ^ n)) * two_mul_hh hn

theorem zT_eq_pow (hn : 2 ≤ n) : zT (n := n) (by omega) = r1T n ^ 2 ^ (n - 1) :=
  (r1T_pow hn).symm

theorem x1T_eq_pow (hn : 2 ≤ n) : x1T (n := n) (by omega) = xT n ^ 2 ^ (n - 1) := by
  have h : xT n = el (iv n ![1, 0, -1, 0]) 1
      (by rw [detSum_one_iff, Fin.sum_univ_four]; simp [iv]) := by
    apply el_congr _ _ _ rfl
    funext i
    fin_cases i <;> simp [iv]
  rw [h, el_iv_pow (by omega) (χ := χx1) (by decide) _ (detSum_hv (by omega) (by decide))]
  rfl

end CFSG.LocalAnalysis.Mason73
