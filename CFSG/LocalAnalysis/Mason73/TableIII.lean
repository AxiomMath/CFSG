module

public import CFSG.LocalAnalysis.Mason73.Complement
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

abbrev tzP : Fin81.R0 := ⟨swap 0 3 * swap 1 2, by decide⟩

theorem pv_s23 (e : Fin 4 → ZMod (2 ^ n)) : pv (s23 : Perm (Fin 4)) e = ![e 0, e 1, e 3, e 2] := by
  funext i
  fin_cases i <;> rfl

theorem pv_s01 (e : Fin 4 → ZMod (2 ^ n)) : pv (s01 : Perm (Fin 4)) e = ![e 1, e 0, e 2, e 3] := by
  funext i
  fin_cases i <;> rfl

theorem pv_zP (e : Fin 4 → ZMod (2 ^ n)) : pv (zP : Perm (Fin 4)) e = ![e 1, e 0, e 3, e 2] := by
  funext i
  fin_cases i <;> rfl

theorem pv_tP (e : Fin 4 → ZMod (2 ^ n)) : pv (tP : Perm (Fin 4)) e = ![e 2, e 3, e 0, e 1] := by
  funext i
  fin_cases i <;> rfl

theorem pv_tzP (e : Fin 4 → ZMod (2 ^ n)) : pv (tzP : Perm (Fin 4)) e = ![e 3, e 2, e 1, e 0] := by
  funext i
  fin_cases i <;> rfl

theorem isConst_of_forall_eq {e : Fin 4 → ZMod (2 ^ n)} (κ : ZMod (2 ^ n)) (h : ∀ i, e i = κ) :
    IsConst e := fun i j => (h i).trans (h j).symm

theorem isConst_of_eq_four {e : Fin 4 → ZMod (2 ^ n)} (κ : ZMod (2 ^ n)) (h0 : e 0 = κ)
    (h1 : e 1 = κ) (h2 : e 2 = κ) (h3 : e 3 = κ) : IsConst e :=
  isConst_of_forall_eq κ fun i => by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem isConst_of_el_mul_self (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (hd : detSum d π) (h2 : el d π hd * el d π hd = 1) : IsConst (d + pv (π : Perm (Fin 4)) d) := by
  rw [el_mul, ← el_zero_one, el_eq_el_iff hn, zero_sub, isConst_neg_iff] at h2
  exact h2.2

theorem isConj_el_of_isConst (hn : 2 ≤ n) {d r e : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (hd : detSum d π) (hr : detSum r π) (he : detSum e 1)
    (hc : IsConst (r - d - (e - pv (π : Perm (Fin 4)) e))) :
    IsConj (el d π hd) (el r π hr) := by
  rw [isConj_iff]
  refine ⟨el e 1 he, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, el_mul, el_mul, el_eq_el_iff hn]
  refine ⟨by simp, ?_⟩
  have : (r + pv (π : Perm (Fin 4)) e) - (e + pv ((1 : Fin81.R0) : Perm (Fin 4)) d) =
      r - d - (e - pv (π : Perm (Fin 4)) e) := by
    rw [OneMemClass.coe_one, pv_one]
    abel
  rw [this]
  exact hc

@[expose] def wT (n : ℕ) : L4Model n :=
  el ![-3, 1, 1, 1] 1 (by rw [detSum_one_iff, Fin.sum_univ_four]; simp; ring)

@[expose] def yT (n : ℕ) : L4Model n :=
  el ![1, 0, 0, -1] 1 (by rw [detSum_one_iff, Fin.sum_univ_four]; simp)

theorem detSum_uw1 (hn : 3 ≤ n) : detSum (fun _ : Fin 4 => ss n) s23 := by
  rw [detSum, sgnH_s23 (by omega), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, four_mul_ss hn, hh_add_hh (by omega)]

@[expose] def uw1T (hn : 3 ≤ n) : L4Model n := el (fun _ => ss n) s23 (detSum_uw1 hn)

theorem detSum_uvxy (hn : 1 ≤ n) : detSum (![hh n, 0, 1, hh n - 1] : Fin 4 → ZMod (2 ^ n)) zP := by
  rw [detSum, sgnH_even (by decide), Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  linear_combination hh_add_hh hn

@[expose] def uvxyT (hn : 1 ≤ n) : L4Model n := el ![hh n, 0, 1, hh n - 1] zP (detSum_uvxy hn)

theorem detSum_tx : detSum (![-1, 0, 1, 0] : Fin 4 → ZMod (2 ^ n)) tP := by
  rw [detSum, sgnH_even (by decide), Fin.sum_univ_four]
  simp

@[expose] def txT (n : ℕ) : L4Model n := el ![-1, 0, 1, 0] tP detSum_tx

theorem yT_pow (hn : 2 ≤ n) : yT n ^ 2 ^ (n - 1) = y1T (by omega) := by
  rw [yT, y1T, el_one_pow, el_eq_el_iff hn]
  have h2 := hh_add_hh (n := n) (by omega)
  refine ⟨rfl, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
    simp only [Pi.sub_apply, Pi.smul_apply, hv, Matrix.cons_val, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply, Nat.cast_one,
      Nat.cast_zero, mul_one, mul_zero] <;>
    first | ring1 | linear_combination h2 | linear_combination -h2

theorem uT_mul_w1T (hn : 3 ≤ n) : uT (n := n) (by omega) * w1T hn = uw1T hn := by
  rw [uT, w1T, uw1T, el_mul, el_eq_el_iff (by omega), pv_s23]
  have h2 := hh_add_hh (n := n) (by omega)
  refine ⟨mul_one _, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
    simp only [Pi.sub_apply, Pi.add_apply, wv, hv, Matrix.cons_val, Nat.cast_one,
      Nat.cast_zero, mul_one, mul_zero] <;>
    first | ring1 | linear_combination h2 | linear_combination -h2

theorem two_mul_zL4 (hn : 2 ≤ n) : 2 * zL4 n = hh n := by
  rw [zL4, hh, show (2 : ZMod (2 ^ n)) = ((2 : ℕ) : ZMod (2 ^ n)) by norm_num, ← Nat.cast_mul]
  congr 1
  rw [← pow_succ']
  congr 1
  omega

theorem exists_eq_two_mul_or (x : ZMod (2 ^ n)) :
    ∃ k : ZMod (2 ^ n), x = 2 * k ∨ x = 2 * k + 1 := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  refine ⟨((x.val / 2 : ℕ) : ZMod (2 ^ n)), ?_⟩
  have h := Nat.div_add_mod x.val 2
  rcases Nat.mod_two_eq_zero_or_one x.val with h0 | h1
  · left
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← h, h0]
    push_cast
    ring
  · right
    conv_lhs => rw [← ZMod.natCast_zmod_val x, ← h, h1]
    push_cast
    ring

theorem detSum_s23_iff {d : Fin 4 → ZMod (2 ^ n)} (hn : 1 ≤ n) :
    detSum d s23 ↔ d 0 + d 1 + d 2 + d 3 + hh n = 0 := by
  rw [detSum, sgnH_s23 hn, Fin.sum_univ_four]

theorem detSum_even_iff {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (hπ : Perm.sign (π : Perm (Fin 4)) = 1) : detSum d π ↔ d 0 + d 1 + d 2 + d 3 = 0 := by
  rw [detSum, sgnH_even hπ, Fin.sum_univ_four, add_zero]

theorem el_s23_mul_self (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d s23)
    (h2 : el d s23 hd * el d s23 hd = 1) : d 0 + d 0 = d 1 + d 1 ∧ d 0 + d 0 = d 2 + d 3 := by
  have H := isConst_of_el_mul_self hn hd h2
  rw [pv_s23] at H
  have h01 := H 0 1
  have h02 := H 0 2
  simp only [Pi.add_apply, Matrix.cons_val] at h01 h02
  exact ⟨h01, h02⟩

theorem isConj_el_s23_uw1T (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d s23)
    (h2 : el d s23 hd * el d s23 hd = 1) (hd1 : d 1 = d 0) :
    IsConj (el d s23 hd) (uw1T hn) := by
  have hd3 : d 3 = d 0 + d 0 - d 2 := by linear_combination -(el_s23_mul_self (by omega) hd h2).2
  rw [uw1T]
  refine isConj_el_of_isConst (by omega) hd (detSum_uw1 hn)
    (e := ![0, -(d 0 - d 2), d 0 - d 2, 0]) ?_ ?_
  · rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    ring
  · rw [pv_s23]
    refine isConst_of_eq_four (ss n - d 0) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Matrix.cons_val] <;> (try simp only [hd1, hd3]) <;> ring1

theorem isConj_el_s23_uT (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d s23)
    (h2 : el d s23 hd * el d s23 hd = 1) (hd1 : d 1 = d 0 + hh n) :
    IsConj (el d s23 hd) (uT (by omega)) := by
  have hd3 : d 3 = d 0 + d 0 - d 2 := by linear_combination -(el_s23_mul_self (by omega) hd h2).2
  have hh2 := hh_add_hh (n := n) (by omega)
  rw [uT]
  refine isConj_el_of_isConst (by omega) hd _
    (e := ![0, -(d 0 - d 2 + hh n), d 0 - d 2 + hh n, 0]) ?_ ?_
  · rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    ring
  · rw [pv_s23]
    refine isConst_of_eq_four (hh n - d 0) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one,
        mul_zero] <;> (try simp only [hd1, hd3]) <;>
      first | ring1 | linear_combination hh2 | linear_combination -hh2

theorem isConj_el_s23 (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d s23)
    (h2 : el d s23 hd * el d s23 hd = 1) :
    IsConj (el d s23 hd) (uT (by omega)) ∨ IsConj (el d s23 hd) (uw1T hn) := by
  obtain ⟨b, hb, hb'⟩ := exists_hh_of_two_mul (by omega) (x := d 1 - d 0)
    (by linear_combination -(el_s23_mul_self (by omega) hd h2).1)
  interval_cases b
  · simp only [Nat.cast_zero, mul_zero] at hb'
    exact Or.inr (isConj_el_s23_uw1T hn hd h2 (by linear_combination hb'))
  · simp only [Nat.cast_one, mul_one] at hb'
    exact Or.inl (isConj_el_s23_uT hn hd h2 (by linear_combination hb'))

theorem el_zP_mul_self (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d zP)
    (h2 : el d zP hd * el d zP hd = 1) :
    d 0 + d 1 = d 2 + d 3 ∧ ∃ b : ℕ, b < 2 ∧ d 0 + d 1 = hh n * (b : ZMod (2 ^ n)) := by
  have H := isConst_of_el_mul_self hn hd h2
  rw [pv_zP] at H
  have h02 := H 0 2
  simp only [Pi.add_apply, Matrix.cons_val] at h02
  have hsum := (detSum_even_iff (by decide)).1 hd
  exact ⟨h02, exists_hh_of_two_mul (by omega) (by linear_combination hsum + h02)⟩

theorem isConj_el_zP_uvT (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d zP)
    (h2 : el d zP hd * el d zP hd = 1) {k : ZMod (2 ^ n)} (hk : d 0 - d 2 = 2 * k) :
    IsConj (el d zP hd) (uvT (by omega)) := by
  obtain ⟨h02, b, -, hκ⟩ := el_zP_mul_self (by omega) hd h2
  have hc := two_mul_zL4 (n := n) (by omega)
  have h4 := four_mul_zL4 n
  set κ₂ : ZMod (2 ^ n) := zL4 n * (b : ZMod (2 ^ n)) with hκ₂
  have hd1 : d 1 = 2 * κ₂ - d 0 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ
  have hd3 : d 3 = 2 * κ₂ - d 2 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ - h02
  have hh' : hh n = 2 * zL4 n := hc.symm
  have hd0 : d 0 = 2 * k + d 2 := by linear_combination hk
  rw [uvT]
  refine isConj_el_of_isConst (by omega) hd _
    (e := ![(zL4 n - d 0 + κ₂) - (-k - d 2 + κ₂), -(-k - d 2 + κ₂), -zL4 n - d 2 + κ₂, 0]) ?_ ?_
  · rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    rw [hd0]
    ring
  · rw [pv_zP]
    refine isConst_of_eq_four (zL4 n - κ₂) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one,
        mul_zero] <;> (try simp only [hd1, hd3, hd0, hh']) <;>
      first | ring1 | linear_combination h4 | linear_combination -h4

theorem isConj_el_zP_uvxyT (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d zP)
    (h2 : el d zP hd * el d zP hd = 1) {k : ZMod (2 ^ n)} (hk : d 0 - d 2 = 2 * k + 1) :
    IsConj (el d zP hd) (uvxyT (by omega)) := by
  obtain ⟨h02, b, -, hκ⟩ := el_zP_mul_self (by omega) hd h2
  have hc := two_mul_zL4 (n := n) (by omega)
  have h4 := four_mul_zL4 n
  set κ₂ : ZMod (2 ^ n) := zL4 n * (b : ZMod (2 ^ n)) with hκ₂
  have hd1 : d 1 = 2 * κ₂ - d 0 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ
  have hd3 : d 3 = 2 * κ₂ - d 2 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ - h02
  have hh' : hh n = 2 * zL4 n := hc.symm
  have hd0 : d 0 = 2 * k + 1 + d 2 := by linear_combination hk
  rw [uvxyT]
  refine isConj_el_of_isConst (by omega) hd _
    (e := ![(zL4 n - d 0 + κ₂) - (-k - d 2 + κ₂), -(-k - d 2 + κ₂), 1 - zL4 n - d 2 + κ₂, 0])
    ?_ ?_
  · rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    rw [hd0]
    ring
  · rw [pv_zP]
    refine isConst_of_eq_four (zL4 n - κ₂) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Matrix.cons_val] <;> (try simp only [hd1, hd3, hd0, hh']) <;>
      first | ring1 | linear_combination h4 | linear_combination -h4

theorem isConj_el_zP (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d zP)
    (h2 : el d zP hd * el d zP hd = 1) :
    IsConj (el d zP hd) (uvT (by omega)) ∨ IsConj (el d zP hd) (uvxyT (by omega)) := by
  obtain ⟨k, hk | hk⟩ := exists_eq_two_mul_or (d 0 - d 2)
  · exact Or.inl (isConj_el_zP_uvT hn hd h2 hk)
  · exact Or.inr (isConj_el_zP_uvxyT hn hd h2 hk)

theorem el_tP_mul_self (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d tP)
    (h2 : el d tP hd * el d tP hd = 1) :
    d 0 + d 2 = d 1 + d 3 ∧ ∃ b : ℕ, b < 2 ∧ d 0 + d 2 = hh n * (b : ZMod (2 ^ n)) := by
  have H := isConst_of_el_mul_self hn hd h2
  rw [pv_tP] at H
  have h01 := H 0 1
  simp only [Pi.add_apply, Matrix.cons_val] at h01
  have hsum := (detSum_even_iff (by decide)).1 hd
  exact ⟨h01, exists_hh_of_two_mul (by omega) (by linear_combination hsum + h01)⟩

theorem isConj_el_tP_tT (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d tP)
    (h2 : el d tP hd * el d tP hd = 1) {k : ZMod (2 ^ n)} (hk : d 1 - d 0 = 2 * k) :
    IsConj (el d tP hd) (tT (by omega)) := by
  obtain ⟨h01, b, -, hκ⟩ := el_tP_mul_self (by omega) hd h2
  have hc := two_mul_zL4 (n := n) (by omega)
  have h4 := four_mul_zL4 n
  set κ₂ : ZMod (2 ^ n) := zL4 n * (b : ZMod (2 ^ n)) with hκ₂
  have hd2 : d 2 = 2 * κ₂ - d 0 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ
  have hd3 : d 3 = 2 * κ₂ - d 1 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ - h01
  have hd1 : d 1 = d 0 + 2 * k := by linear_combination hk
  rw [tT]
  refine isConj_el_of_isConst (by omega) hd _
    (e := ![(κ₂ - d 0) - (κ₂ - d 0 - k), κ₂ - d 1, -(κ₂ - d 0 - k), 0]) ?_ ?_
  · rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    rw [hd1]
    ring
  · rw [pv_tP]
    refine isConst_of_eq_four (-κ₂) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one,
        mul_zero] <;> (try simp only [hd2, hd3, hd1]) <;>
      first | ring1 | linear_combination h4 | linear_combination -h4

theorem isConj_el_tP_txT (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d tP)
    (h2 : el d tP hd * el d tP hd = 1) {k : ZMod (2 ^ n)} (hk : d 1 - d 0 = 2 * k + 1) :
    IsConj (el d tP hd) (txT n) := by
  obtain ⟨h01, b, -, hκ⟩ := el_tP_mul_self (by omega) hd h2
  have hc := two_mul_zL4 (n := n) (by omega)
  have h4 := four_mul_zL4 n
  set κ₂ : ZMod (2 ^ n) := zL4 n * (b : ZMod (2 ^ n)) with hκ₂
  have hd2 : d 2 = 2 * κ₂ - d 0 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ
  have hd3 : d 3 = 2 * κ₂ - d 1 := by rw [hκ₂, ← mul_assoc, hc]; linear_combination hκ - h01
  have hd1 : d 1 = d 0 + 2 * k + 1 := by linear_combination hk
  rw [txT]
  refine isConj_el_of_isConst (by omega) hd _
    (e := ![(-1 - d 0 + κ₂) - (-1 - d 0 - k + κ₂), κ₂ - d 1, -(-1 - d 0 - k + κ₂), 0]) ?_ ?_
  · rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    rw [hd1]
    ring
  · rw [pv_tP]
    refine isConst_of_eq_four (-κ₂) ?_ ?_ ?_ ?_ <;>
      simp only [Pi.sub_apply, Matrix.cons_val] <;> (try simp only [hd2, hd3, hd1]) <;>
      first | ring1 | linear_combination h4 | linear_combination -h4

theorem isConj_el_tP (hn : 3 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (hd : detSum d tP)
    (h2 : el d tP hd * el d tP hd = 1) :
    IsConj (el d tP hd) (tT (by omega)) ∨ IsConj (el d tP hd) (txT n) := by
  obtain ⟨k, hk | hk⟩ := exists_eq_two_mul_or (d 1 - d 0)
  · exact Or.inl (isConj_el_tP_tT hn hd h2 hk)
  · exact Or.inr (isConj_el_tP_txT hn hd h2 hk)

theorem piT_eq_of_mul_self {μ : L4Model n} (h : μ * μ = 1) :
    piT μ = 1 ∨ piT μ = s23 ∨ piT μ = s01 ∨ piT μ = zP ∨ piT μ = tP ∨ piT μ = tzP := by
  have h' : piT μ * piT μ = 1 := by rw [← map_mul, h, map_one]
  generalize piT μ = π at h' ⊢
  revert π
  decide

theorem conj_mul_self {G : Type*} [Group G] {g μ : G} (h : μ * μ = 1) :
    g * μ * g⁻¹ * (g * μ * g⁻¹) = 1 := by
  calc g * μ * g⁻¹ * (g * μ * g⁻¹) = g * (μ * μ) * g⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem piT_uT (hn : 1 ≤ n) : piT (uT (n := n) hn) = s23 := rfl
theorem piT_vT (hn : 1 ≤ n) : piT (vT (n := n) hn) = s01 := rfl
theorem piT_tT (hn : 1 ≤ n) : piT (tT (n := n) hn) = tP := rfl
theorem piT_uvT (hn : 1 ≤ n) : piT (uvT (n := n) hn) = zP := rfl

theorem isConj_uT_or_uw1T (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = s23 ∨ piT μ = s01) : IsConj μ (uT (by omega)) ∨ IsConj μ (uw1T hn) := by
  have key : ∀ ν : L4Model n, ν * ν = 1 → piT ν = s23 →
      IsConj ν (uT (by omega)) ∨ IsConj ν (uw1T hn) := by
    intro ν hν hπν
    obtain ⟨d, π, hd, rfl⟩ := exists_eq_el ν
    rw [piT_el] at hπν
    subst hπν
    exact isConj_el_s23 hn hd hν
  rcases hπ with hπ | hπ
  · exact key μ h2 hπ
  · have hμν : IsConj μ (tT (n := n) (by omega) * μ * (tT (by omega))⁻¹) :=
      isConj_iff.mpr ⟨_, rfl⟩
    have hνπ : piT (tT (n := n) (by omega) * μ * (tT (by omega))⁻¹) = s23 := by
      rw [map_mul, map_mul, map_inv, hπ, piT_tT]
      decide
    rcases key _ (conj_mul_self h2) hνπ with h | h
    · exact Or.inl (hμν.trans h)
    · exact Or.inr (hμν.trans h)

theorem isConj_uvT_or_uvxyT (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1) (hπ : piT μ = zP) :
    IsConj μ (uvT (by omega)) ∨ IsConj μ (uvxyT (by omega)) := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hπ
  subst hπ
  exact isConj_el_zP hn hd h2

theorem isConj_tT_or_txT (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = tP ∨ piT μ = tzP) : IsConj μ (tT (by omega)) ∨ IsConj μ (txT n) := by
  have key : ∀ ν : L4Model n, ν * ν = 1 → piT ν = tP →
      IsConj ν (tT (by omega)) ∨ IsConj ν (txT n) := by
    intro ν hν hπν
    obtain ⟨d, π, hd, rfl⟩ := exists_eq_el ν
    rw [piT_el] at hπν
    subst hπν
    exact isConj_el_tP hn hd hν
  rcases hπ with hπ | hπ
  · exact key μ h2 hπ
  · have hμν : IsConj μ (uT (n := n) (by omega) * μ * (uT (by omega))⁻¹) :=
      isConj_iff.mpr ⟨_, rfl⟩
    have hνπ : piT (uT (n := n) (by omega) * μ * (uT (by omega))⁻¹) = tP := by
      rw [map_mul, map_mul, map_inv, hπ, piT_uT]
      decide
    rcases key _ (conj_mul_self h2) hνπ with h | h
    · exact Or.inl (hμν.trans h)
    · exact Or.inr (hμν.trans h)

theorem isConj_el_wv_w1T (hn : 3 ≤ n) {χ : Fin 4 → ℕ} (hχ : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 1)
    {d : Fin 4 → ZMod (2 ^ n)} {σ : Fin81.R0} (hd : detSum d σ)
    (hpat : ∀ i j, ((![1, 0, 0, 0] : Fin 4 → ℕ) i + χ ((σ : Perm (Fin 4))⁻¹ j)) % 2 =
      ((![1, 0, 0, 0] : Fin 4 → ℕ) j + χ ((σ : Perm (Fin 4))⁻¹ i)) % 2) :
    IsConj (el (wv n χ) 1 (detSum_wv hn hχ)) (w1T hn) := by
  rw [isConj_iff]
  refine ⟨el d σ hd, ?_⟩
  rw [el_conj (by omega), w1T, el_eq_el_iff (by omega)]
  refine ⟨rfl, ?_⟩
  have : wv n ![1, 0, 0, 0] - pv (σ : Perm (Fin 4)) (wv n χ) =
      hv n ![1, 0, 0, 0] - hv n (fun i => χ ((σ : Perm (Fin 4))⁻¹ i)) := by
    funext i
    simp only [Pi.sub_apply, pv, wv, hv]
    ring
  rw [this, hv_sub_hv_isConst_iff (by omega)]
  exact hpat

theorem isConj_y1T_x1T (hn : 2 ≤ n) : IsConj (y1T (n := n) (by omega)) (x1T (by omega)) := by
  rw [isConj_iff]
  refine ⟨uT (by omega), ?_⟩
  rw [uT, y1T, x1T, el_conj hn, el_eq_el_iff hn]
  refine ⟨rfl, ?_⟩
  rw [pv_hv, hv_sub_hv_isConst_iff (by omega)]
  decide

theorem detSum_zero_tzP : detSum (0 : Fin 4 → ZMod (2 ^ n)) tzP := by
  rw [detSum_even_iff (by decide)]
  simp

theorem isConj_of_mem_A (hn : 3 ≤ n) {μ : L4Model n} (hA : μ ∈ A n) (h1 : μ ≠ 1)
    (h2 : μ * μ = 1) :
    IsConj μ (zT (by omega)) ∨ IsConj μ (x1T (by omega)) ∨ IsConj μ (w1T hn) := by
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn hA h2
  obtain ⟨a, b, c⟩ := p
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp only [Fin.zero_eta, Fin.mk_one] at h1 ⊢
  · exact absurd (omegaEl_zero hn) h1
  · right; right
    rw [omegaEl, dif_neg (by decide)]
    exact isConj_el_wv_w1T hn (by decide) detSum_zero_tzP (by decide)
  · right; right
    rw [omegaEl, dif_neg (by decide)]
    exact isConj_el_wv_w1T hn (by decide)
      (detSum_hv_even (n := n) (χ := ![0, 0, 0, 0]) (π := tP) (by omega) (by decide) (by decide))
      (by decide)
  · left
    rw [← zT_eq_omegaEl hn]
  · right; right
    rw [omegaEl, dif_neg (by decide)]
    exact isConj_el_wv_w1T hn (by decide)
      (detSum_hv_odd (n := n) (χ := ![0, 0, 1, 0]) (by omega) (sgnH_s01 (by omega)) (by decide))
      (by decide)
  · right; left
    rw [← x1T_eq_omegaEl hn]
  · right; left
    rw [← y1T_eq_omegaEl hn]
    exact isConj_y1T_x1T (by omega)
  · right; right
    rw [← w1T_eq_omegaEl hn]

theorem isConj_rep (hn : 3 ≤ n) {μ : L4Model n} (h1 : μ ≠ 1) (h2 : μ * μ = 1) :
    IsConj μ (zT (by omega)) ∨ IsConj μ (x1T (by omega)) ∨ IsConj μ (w1T hn) ∨
      IsConj μ (uT (by omega)) ∨ IsConj μ (uw1T hn) ∨ IsConj μ (uvT (by omega)) ∨
      IsConj μ (uvxyT (by omega)) ∨ IsConj μ (tT (by omega)) ∨ IsConj μ (txT n) := by
  rcases piT_eq_of_mul_self h2 with hπ | hπ | hπ | hπ | hπ | hπ
  · rcases isConj_of_mem_A hn (mem_A_iff.2 hπ) h1 h2 with h | h | h <;>
      simp only [h, true_or, or_true]
  · rcases isConj_uT_or_uw1T hn h2 (Or.inl hπ) with h | h <;> simp only [h, true_or, or_true]
  · rcases isConj_uT_or_uw1T hn h2 (Or.inr hπ) with h | h <;> simp only [h, true_or, or_true]
  · rcases isConj_uvT_or_uvxyT hn h2 hπ with h | h <;> simp only [h, true_or, or_true]
  · rcases isConj_tT_or_txT hn h2 (Or.inl hπ) with h | h <;> simp only [h, true_or, or_true]
  · rcases isConj_tT_or_txT hn h2 (Or.inr hπ) with h | h <;> simp only [h, true_or, or_true]

theorem card_centralizer_conj {G : Type*} [Group G] (c μ : G) :
    Nat.card (centralizer {c * μ * c⁻¹}) = Nat.card (centralizer {μ}) := by
  have h : centralizer {c * μ * c⁻¹} = (centralizer {μ}).map (MulAut.conj c).toMonoidHom := by
    ext x
    simp only [mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hx
      refine ⟨c⁻¹ * x * c, ?_, by group⟩
      calc c⁻¹ * x * c * μ = c⁻¹ * (x * (c * μ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * μ * c⁻¹) * x) * c := by rw [hx]
        _ = μ * (c⁻¹ * x * c) := by group
    · rintro ⟨y, hy, rfl⟩
      calc c * y * c⁻¹ * (c * μ * c⁻¹) = c * (y * μ) * c⁻¹ := by group
        _ = c * (μ * y) * c⁻¹ := by rw [hy]
        _ = c * μ * c⁻¹ * (c * y * c⁻¹) := by group
  rw [h, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem card_centralizer_eq_of_isConj {G : Type*} [Group G] {μ ν : G} (h : IsConj μ ν) :
    Nat.card (centralizer {μ}) = Nat.card (centralizer {ν}) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (card_centralizer_conj c μ).symm

theorem card_map_piT_centralizer_le (μ : L4Model n) (s : Finset Fin81.R0)
    (hs : ∀ σ : Fin81.R0, σ * piT μ = piT μ * σ → σ ∈ s) :
    Nat.card ((centralizer {μ}).map piT) ≤ s.card := by
  have hsub : (((centralizer {μ}).map piT : Subgroup Fin81.R0) : Set Fin81.R0) ⊆ ↑s := by
    rintro _ ⟨g, hg, rfl⟩
    apply hs
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hg
    rw [← map_mul, ← map_mul, hg]
  calc Nat.card ((centralizer {μ}).map piT) =
        (((centralizer {μ}).map piT : Subgroup Fin81.R0) : Set Fin81.R0).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ (↑s : Set Fin81.R0).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = s.card := Set.ncard_coe_finset _

theorem not_mem_A_of_piT_ne {μ : L4Model n} (h : piT μ ≠ 1) : μ ∉ A n := fun hA =>
  h (mem_A_iff.1 hA)

theorem card_centralizer_le_of_piT_s23 (hn : 2 ≤ n) {μ : L4Model n}
    (hπ : piT μ = s23 ∨ piT μ = s01) : Nat.card (centralizer {μ}) ≤ 2 ^ (2 * n) := by
  rw [card_eq_card_inf_A_mul]
  have hA : μ ∉ A n := not_mem_A_of_piT_ne (by rcases hπ with h | h <;> rw [h] <;> decide)
  have h1 : Nat.card (centralizer {μ} ⊓ A n : Subgroup (L4Model n)) ≤ 2 ^ (2 * n - 2) := by
    rw [inf_comm]
    exact card_centA_le hn hA
  have h2 : Nat.card ((centralizer {μ}).map piT) ≤ 4 := by
    rcases hπ with h | h
    · exact (card_map_piT_centralizer_le μ {1, s23, s01, zP} (by rw [h]; decide)).trans
        (by decide)
    · exact (card_map_piT_centralizer_le μ {1, s23, s01, zP} (by rw [h]; decide)).trans
        (by decide)
  calc _ ≤ 2 ^ (2 * n - 2) * 4 := Nat.mul_le_mul h1 h2
    _ = 2 ^ (2 * n) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega

theorem card_centralizer_le_of_piT_zP (hn : 2 ≤ n) {μ : L4Model n} (hπ : piT μ = zP) :
    Nat.card (centralizer {μ}) ≤ 2 ^ (n + 3) := by
  rw [card_eq_card_inf_A_mul]
  have h1 : Nat.card (centralizer {μ} ⊓ A n : Subgroup (L4Model n)) ≤ 2 ^ n := by
    rw [inf_comm]
    exact card_centA_le_of_fpf hn (by rw [hπ]; decide)
  have h2 : Nat.card ((centralizer {μ}).map piT) ≤ 8 := by
    rw [← Fin81.card_R0]
    exact Subgroup.card_le_card_group _
  calc _ ≤ 2 ^ n * 8 := Nat.mul_le_mul h1 h2
    _ = 2 ^ (n + 3) := by rw [pow_add]; norm_num

theorem card_centralizer_le_of_piT_tP (hn : 2 ≤ n) {μ : L4Model n}
    (hπ : piT μ = tP ∨ piT μ = tzP) : Nat.card (centralizer {μ}) ≤ 2 ^ (n + 2) := by
  rw [card_eq_card_inf_A_mul]
  have h1 : Nat.card (centralizer {μ} ⊓ A n : Subgroup (L4Model n)) ≤ 2 ^ n := by
    rw [inf_comm]
    exact card_centA_le_of_fpf hn (by rcases hπ with h | h <;> rw [h] <;> decide)
  have h2 : Nat.card ((centralizer {μ}).map piT) ≤ 4 := by
    rcases hπ with h | h
    · exact (card_map_piT_centralizer_le μ {1, tP, zP, tzP} (by rw [h]; decide)).trans
        (by decide)
    · exact (card_map_piT_centralizer_le μ {1, tP, zP, tzP} (by rw [h]; decide)).trans
        (by decide)
  calc _ ≤ 2 ^ n * 4 := Nat.mul_le_mul h1 h2
    _ = 2 ^ (n + 2) := by rw [pow_add]; norm_num

theorem le_card_centA_of_piT_s23 (hn : 2 ≤ n) {μ : L4Model n} (hπ : piT μ = s23) :
    2 ^ (2 * n - 2) ≤ Nat.card (centA μ) := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hπ
  subst hπ
  have hle : (coordDiff (n := n) 3 2).ker ≤ (centA (el d s23 hd)).comap beta := by
    intro e he
    rw [MonoidHom.mem_ker] at he
    have he' : vec e 3 - vec e 2 = 0 := by
      have := congrArg Multiplicative.toAdd he
      simpa [coordDiff] using this
    refine Subgroup.mem_comap.2 (Subgroup.mem_inf.2 ⟨beta_mem_A e, ?_⟩)
    rw [mem_centralizer_singleton_iff, beta_apply]
    refine ((el_comm_diag_iff hn hd _).2 ?_).symm
    rw [pv_s23]
    refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;> simp only [Pi.sub_apply, Matrix.cons_val] <;>
      first | ring1 | linear_combination he' | linear_combination -he'
  have h1 := Subgroup.card_le_of_le hle
  rw [card_ker_coordDiff (by decide), card_comap_beta hn inf_le_left] at h1
  have h2 : 2 ^ (2 * n) = 4 * 2 ^ (2 * n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h2] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by norm_num)

theorem le_card_centralizer_of_piT_s23 (hn : 2 ≤ n) {μ : L4Model n} (hπ : piT μ = s23)
    {ν : L4Model n} (hν : piT ν = s01) (hμν : ν * μ = μ * ν) :
    2 ^ (2 * n) ≤ Nat.card (centralizer {μ}) := by
  rw [card_eq_card_inf_A_mul]
  have h1 : 2 ^ (2 * n - 2) ≤ Nat.card (centralizer {μ} ⊓ A n : Subgroup (L4Model n)) := by
    rw [inf_comm]
    exact le_card_centA_of_piT_s23 hn hπ
  have h2 : 4 ≤ Nat.card ((centralizer {μ}).map piT) := by
    have hμ : piT μ ∈ (centralizer {μ}).map piT :=
      ⟨μ, mem_centralizer_singleton_iff.2 rfl, rfl⟩
    have hν' : piT ν ∈ (centralizer {μ}).map piT := ⟨ν, mem_centralizer_singleton_iff.2 hμν, rfl⟩
    rw [hπ] at hμ
    rw [hν] at hν'
    have h4 : 4 ≤ (((centralizer {μ}).map piT : Subgroup Fin81.R0) : Set Fin81.R0).ncard :=
      four_le_ncard (Subgroup.one_mem _) hμ hν' (Subgroup.mul_mem _ hμ hν') (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (Set.toFinite _)
    exact h4.trans_eq (Nat.card_coe_set_eq _).symm
  calc 2 ^ (2 * n) = 2 ^ (2 * n - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
    _ ≤ _ := Nat.mul_le_mul h1 h2

theorem vT_mul_uT_comm (hn : 2 ≤ n) : vT (n := n) (by omega) * uT (by omega) =
    uT (by omega) * vT (by omega) := by
  rw [vT_mul_uT hn, uT_mul_vT hn]

theorem detSum_vx1 (hn : 1 ≤ n) : detSum (hv n ![0, 1, 0, 0]) s01 :=
  detSum_hv_odd hn (sgnH_s01 hn) (by decide)

theorem vx1_mul_uw1T_comm (hn : 3 ≤ n) :
    el (hv n ![0, 1, 0, 0]) s01 (detSum_vx1 (by omega)) * uw1T hn =
      uw1T hn * el (hv n ![0, 1, 0, 0]) s01 (detSum_vx1 (by omega)) := by
  rw [uw1T, el_mul, el_mul, el_eq_el_iff (by omega), pv_s01, pv_s23]
  refine ⟨by decide, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] <;> ring1

theorem card_centralizer_uT (hn : 2 ≤ n) :
    Nat.card (centralizer {uT (n := n) (by omega)}) = 2 ^ (2 * n) :=
  le_antisymm (card_centralizer_le_of_piT_s23 hn (Or.inl rfl))
    (le_card_centralizer_of_piT_s23 hn rfl (piT_vT _) (vT_mul_uT_comm hn))

theorem card_centralizer_uw1T (hn : 3 ≤ n) : Nat.card (centralizer {uw1T hn}) = 2 ^ (2 * n) :=
  le_antisymm (card_centralizer_le_of_piT_s23 (by omega) (Or.inl rfl))
    (le_card_centralizer_of_piT_s23 (by omega) rfl rfl (vx1_mul_uw1T_comm hn))

theorem card_centralizer_of_piT_s23 (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = s23 ∨ piT μ = s01) : Nat.card (centralizer {μ}) = 2 ^ (2 * n) := by
  rcases isConj_uT_or_uw1T hn h2 hπ with h | h
  · rw [card_centralizer_eq_of_isConj h, card_centralizer_uT (by omega)]
  · rw [card_centralizer_eq_of_isConj h, card_centralizer_uw1T hn]

end CFSG.LocalAnalysis.Mason73
