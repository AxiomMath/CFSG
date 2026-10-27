module

public import Certificates.Data.Kernel.F2Set24
public import CFSG.Sporadic.Schreier.Co1OrbEnum

public section

namespace CFSG.KS.F2Set24

open CFSG.KC.F2Set24 CFSG.Sporadic.Co1Schreier Matrix
open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)
open CFSG.Sporadic.SmallF2.Native (vecMulN)

inductive Back (f g : ℕ → ℕ) (r : ℕ) : ℕ → Prop
  | base : Back f g r r
  | sf {v : ℕ} : Back f g r (f v) → Back f g r v
  | sg {v : ℕ} : Back f g r (g v) → Back f g r v

theorem strict_eq {α : Sort*} (y : ℕ) (k : ℕ → α) : strict y k = k y := by
  cases y <;> rfl

theorem beq_mod2 (x : ℕ) : Nat.beq (x % 2) 1 = x.testBit 0 := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> rfl

theorem par_succ (d x : ℕ) : par (d + 1) x = (x.testBit 0 ^^ par d (x / 2)) := by
  change Bool.xor (Nat.beq (x % 2) 1) (par d (x / 2)) = _
  rw [beq_mod2] <;> rfl

theorem xor_div2 (x y : ℕ) : (x ^^^ y) / 2 = x / 2 ^^^ y / 2 :=
  Nat.eq_of_testBit_eq fun i => by simp only [Nat.testBit_div_two, Nat.testBit_xor]

theorem par_xor (d : ℕ) : ∀ x y, par d (x ^^^ y) = (par d x ^^ par d y) := by
  induction d with
  | zero => intro x y; rfl
  | succ d ih =>
    intro x y
    rw [par_succ, par_succ, par_succ, Nat.testBit_xor, xor_div2, ih]
    cases x.testBit 0 <;> cases y.testBit 0 <;> cases par d (x / 2) <;> cases par d (y / 2) <;>
      rfl

theorem par_zero (d : ℕ) : par d 0 = false := by
  induction d with
  | zero => rfl
  | succ d ih => rw [par_succ, Nat.zero_div, ih]; rfl

theorem par_and_shift (L a p k : ℕ) :
    par (L + 1) (a &&& (p >>> k)) =
      ((a.testBit 0 && p.testBit k) ^^ par L (a / 2 &&& (p >>> (k + 1)))) := by
  rw [par_succ]
  have h1 : (a &&& (p >>> k)).testBit 0 = (a.testBit 0 && p.testBit k) := by
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero]
  have h2 : (a &&& (p >>> k)) / 2 = a / 2 &&& (p >>> (k + 1)) := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_shiftRight]
    rw [show k + (i + 1) = k + 1 + i by omega]
  rw [h1, h2]

theorem testBit_add_pow (y t k : ℕ) : (y + 2 ^ (k + 1) * t).testBit k = y.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, pow_succ, mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.add_mul_mod_self_left]

theorem testBit_sub_dvd {k w q : ℕ} (hw : 2 ^ (k + 1) ∣ w) (hq : w ≤ q) :
    (q - w).testBit k = q.testBit k := by
  obtain ⟨t, rfl⟩ := hw
  conv_rhs => rw [show q = (q - 2 ^ (k + 1) * t) + 2 ^ (k + 1) * t by omega]
  rw [testBit_add_pow]

theorem clear_sub {q i : ℕ} (hqi : q.testBit i = false) (hge : 2 ^ i ≤ q) :
    (q - 2 ^ i).testBit i = true := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 ^ i := ⟨q - 2 ^ i, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.add_div_right _ (Nat.two_pow_pos i)] at hqi
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hqi ⊢
  omega

theorem set_sub {q i : ℕ} (hqi : q.testBit i = true) : (q - 2 ^ i).testBit i = false := by
  have hge := Nat.ge_two_pow_of_testBit hqi
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 ^ i := ⟨q - 2 ^ i, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.add_div_right _ (Nat.two_pow_pos i)] at hqi
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hqi ⊢
  omega

theorem xor_clear {x i : ℕ} (hx : x.testBit i = false) : x ^^^ 2 ^ i = x + 2 ^ i := by
  have h0 : x / 2 ^ i % 2 = 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq] at hx
    simp only [decide_eq_false_iff_not] at hx
    omega
  have hl : x % 2 ^ (i + 1) < 2 ^ i := by
    rw [Nat.mod_pow_succ, h0, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_lt _ (Nat.two_pow_pos i)
  have hx' : x = 2 ^ (i + 1) * (x / 2 ^ (i + 1)) + x % 2 ^ (i + 1) := (Nat.div_add_mod x _).symm
  generalize x / 2 ^ (i + 1) = h at hx'
  generalize x % 2 ^ (i + 1) = l at hx' hl
  subst hx'
  have hp : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ, Nat.mul_comm]
  have hl1 : l < 2 ^ (i + 1) := by omega
  have hl2 : l + 2 ^ i < 2 ^ (i + 1) := by omega
  rw [Nat.add_assoc]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hl1, Nat.testBit_two_pow_mul_add _ hl2,
    ← Nat.or_two_pow_eq_add_of_lt hl, Nat.testBit_two_pow]
  split_ifs with hj
  · rw [Nat.testBit_or, Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij
      simp [Nat.testBit_lt_two_pow hl]
    · simp [hij]
  · have hij : i ≠ j := by omega
    simp [hij]

theorem xor_set {q i : ℕ} (hq : q.testBit i = true) : q ^^^ 2 ^ i = q - 2 ^ i := by
  have hge := Nat.ge_two_pow_of_testBit hq
  have h1 := xor_clear (set_sub hq)
  rw [Nat.sub_add_cancel hge] at h1
  calc q ^^^ 2 ^ i = ((q - 2 ^ i) ^^^ 2 ^ i) ^^^ 2 ^ i := by rw [h1]
    _ = q - 2 ^ i := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem and_xor_clear {a i : ℕ} (ha : a.testBit i = false) (v : ℕ) :
    a &&& (v ^^^ 2 ^ i) = a &&& v := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hij : i = j
  · subst hij
    simp [ha]
  · simp [hij]

theorem sub_lt_iff {q i : ℕ} (hi : i < 24) (hq : q.testBit i = true) :
    q - 2 ^ i < 2 ^ 24 ↔ q < 2 ^ 24 := by
  have hr : (q % 2 ^ 24).testBit i = true := by
    rw [Nat.testBit_mod_two_pow]
    simp [hi, hq]
  have h1 := Nat.ge_two_pow_of_testBit hr
  have h2 := Nat.div_add_mod q (2 ^ 24)
  have h3 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  rw [h3] at h1 h2 ⊢
  generalize 2 ^ i = c at h1 ⊢
  omega

def OK (o : ℕ × ℕ) : Prop := o.1 < 24 ∧ o.2.testBit o.1 = false

theorem opApp_eq (o : ℕ × ℕ) (v : ℕ) :
    opApp o v = if par 24 (o.2 &&& v) = true then v ^^^ 2 ^ o.1 else v := by
  unfold opApp
  cases h : par 24 (Nat.land o.2 v) <;> simp_all [Nat.one_shiftLeft]

theorem opApp_invol {o : ℕ × ℕ} (ho : OK o) (v : ℕ) : opApp o (opApp o v) = v := by
  rw [opApp_eq o v]
  split_ifs with h
  · rw [opApp_eq, and_xor_clear ho.2, if_pos h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · rw [opApp_eq, if_neg h]

theorem opApp_xor (o : ℕ × ℕ) (u w : ℕ) : opApp o (u ^^^ w) = opApp o u ^^^ opApp o w := by
  rw [opApp_eq, opApp_eq o u, opApp_eq o w, Nat.and_xor_distrib_left, par_xor]
  cases par 24 (o.2 &&& u) <;> cases par 24 (o.2 &&& w) <;> simp only [Bool.false_xor,
    Bool.xor_false, Bool.true_xor, Bool.xor_true, Bool.not_true, Bool.not_false, if_true,
    if_false, Bool.false_eq_true] <;>
  · apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_xor]
    cases u.testBit j <;> cases w.testBit j <;> cases (2 ^ o.1).testBit j <;> rfl

theorem opApp_zero (o : ℕ × ℕ) : opApp o 0 = 0 := by
  rw [opApp_eq, Nat.and_zero, par_zero]
  rfl

theorem opApp_lt {o : ℕ × ℕ} (ho : OK o) {v : ℕ} (hv : v < 2 ^ 24) : opApp o v < 2 ^ 24 := by
  rw [opApp_eq]
  split_ifs
  · exact Nat.xor_lt_two_pow hv (Nat.pow_lt_pow_right (by norm_num) ho.1)
  · exact hv

theorem opsApp_cons (o : ℕ × ℕ) (ops : List (ℕ × ℕ)) (v : ℕ) :
    opsApp (o :: ops) v = opApp o (opsApp ops v) :=
  strict_eq _ _

theorem opsApp_xor (ops : List (ℕ × ℕ)) (u w : ℕ) :
    opsApp ops (u ^^^ w) = opsApp ops u ^^^ opsApp ops w := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [opsApp_cons, opsApp_cons, opsApp_cons, ih, opApp_xor]

theorem opsApp_zero (ops : List (ℕ × ℕ)) : opsApp ops 0 = 0 := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [opsApp_cons, ih, opApp_zero]

theorem opsApp_lt {ops : List (ℕ × ℕ)} (hok : ∀ o ∈ ops, OK o) {v : ℕ} (hv : v < 2 ^ 24) :
    opsApp ops v < 2 ^ 24 := by
  induction ops with
  | nil => exact hv
  | cons o ops ih =>
    rw [opsApp_cons]
    exact opApp_lt (hok o (List.mem_cons_self ..)) (ih fun o' h => hok o' (List.mem_cons_of_mem _ h))

theorem opsApp_inj {ops : List (ℕ × ℕ)} (hok : ∀ o ∈ ops, OK o) :
    Function.Injective (opsApp ops) := by
  induction ops with
  | nil => exact fun _ _ h => h
  | cons o ops ih =>
    intro u w h
    rw [opsApp_cons, opsApp_cons] at h
    have h' := congrArg (opApp o) h
    rw [opApp_invol (hok o (List.mem_cons_self ..)),
      opApp_invol (hok o (List.mem_cons_self ..))] at h'
    exact ih (fun o' h => hok o' (List.mem_cons_of_mem _ h)) h'

theorem opsWF_ok : ∀ {ops : List (ℕ × ℕ)}, opsWF ops = true → ∀ o ∈ ops, OK o
  | [], _ => by simp
  | o :: ops, h => by
    have h' : (Nat.blt o.1 24 && Nat.blt o.2 W && Nat.beq ((o.2 >>> o.1) % 2) 0 &&
        opsWF ops) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨⟨⟨h1, -⟩, h3⟩, h4⟩ := h'
    intro o' ho'
    rcases List.mem_cons.1 ho' with rfl | ho'
    · refine ⟨h1, ?_⟩
      rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, h3]
      rfl
    · exact opsWF_ok h4 o' ho'

theorem colsOK_spec {ops : List (ℕ × ℕ)} :
    ∀ {cs : List ℕ} {j0 : ℕ}, colsOK ops cs j0 = true →
      ∀ j < cs.length, opsApp ops (2 ^ (j0 + j)) = cs[j]?.getD 0
  | [], _, _ => by simp
  | x :: cs, j0, h => by
    have h' : (Nat.beq (opsApp ops (1 <<< j0)) x && colsOK ops cs (j0 + 1)) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.one_shiftLeft] at h'
    intro j hj
    cases j with
    | zero => simpa using h'.1
    | succ j =>
      have := colsOK_spec h'.2 j (by simpa using hj)
      rw [show j0 + (j + 1) = j0 + 1 + j by omega, this]
      simp

theorem mod_split (v L : ℕ) :
    v % 2 ^ (L + 1) = v % 2 ^ L ^^^ (if v.testBit L = true then 2 ^ L else 0) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
  rcases lt_trichotomy j L with h | rfl | h
  · have h1 : j < L + 1 := by omega
    have h2 : L ≠ j := by omega
    split_ifs <;> simp [h, h1, h2, Nat.testBit_two_pow]
  · split_ifs with hv <;> simp [hv, Nat.testBit_two_pow]
  · have h1 : ¬ j < L + 1 := by omega
    have h1' : ¬ j < L := by omega
    have h2 : L ≠ j := by omega
    split_ifs <;> simp [h1, h1', h2, Nat.testBit_two_pow]

theorem fold_eq (ops : List (ℕ × ℕ)) (R : Array ℕ) (v : ℕ) :
    ∀ L, (∀ j < L, opsApp ops (2 ^ j) = R[j]?.getD 0) →
      (List.range L).foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) 0
        = opsApp ops (v % 2 ^ L)
  | 0, _ => by rw [List.range_zero, List.foldl_nil, pow_zero, Nat.mod_one, opsApp_zero]
  | L + 1, hc => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      fold_eq ops R v L (fun j hj => hc j (by omega)), mod_split, opsApp_xor, ← hc L (by omega)]
    split_ifs <;> simp [opsApp_zero]

theorem opsOK_facts {c : List ℕ} {ops : List (ℕ × ℕ)} (h : opsOK c ops = true) :
    (∀ o ∈ ops, OK o) ∧ ∀ v < 2 ^ 24, opsApp ops v = vecMulN 24 c.toArray v := by
  have h' : (Nat.beq c.length 24 && opsWF ops && colsOK ops c 0) = true := h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  obtain ⟨⟨hlen, hwf⟩, hcols⟩ := h'
  refine ⟨opsWF_ok hwf, fun v hv => ?_⟩
  have hc := colsOK_spec hcols
  unfold vecMulN
  rw [fold_eq ops c.toArray v 24 (fun j hj => by
    rw [List.getElem?_toArray, ← hc j (by omega), Nat.zero_add]), Nat.mod_eq_of_lt hv]

theorem dbl_succ (c w x : ℕ) : dbl (c + 1) w x = dbl c (2 * w) (x ||| (x <<< w)) :=
  strict_eq _ _

theorem dbl_bits {k : ℕ} :
    ∀ (c w x : ℕ), 2 ^ (k + 1) ∣ w → (∀ q, x.testBit q = (decide (q < w) && q.testBit k)) →
      ∀ q, (dbl c w x).testBit q = (decide (q < w * 2 ^ c) && q.testBit k)
  | 0, w, x, _, hx => by
    intro q
    change x.testBit q = _
    rw [hx, pow_zero, Nat.mul_one]
  | c + 1, w, x, hw, hx => by
    rw [dbl_succ]
    have hx' : ∀ q, (x ||| (x <<< w)).testBit q = (decide (q < 2 * w) && q.testBit k) := by
      intro q
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, hx, hx]
      by_cases hq : q < w
      · have : ¬ q ≥ w := by omega
        have h2 : q < 2 * w := by omega
        simp [hq, this, h2]
      · have h1 : q ≥ w := by omega
        rw [testBit_sub_dvd hw h1]
        by_cases h2 : q < 2 * w
        · have h3 : q - w < w := by omega
          simp [hq, h1, h2, h3]
        · have h3 : ¬ q - w < w := by omega
          simp [hq, h1, h2, h3]
    intro q
    rw [dbl_bits c (2 * w) _ (Dvd.dvd.mul_left hw 2) hx' q,
      show 2 * w * 2 ^ c = w * 2 ^ (c + 1) by ring]

theorem pmask_bits {k : ℕ} (hk : k < 24) (q : ℕ) :
    (pmask k).testBit q = (decide (q < 2 ^ 24) && q.testBit k) := by
  unfold pmask
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
  have h0 : ∀ q, (Nat.shiftLeft (2 ^ 2 ^ k - 1) (2 ^ k)).testBit q =
      (decide (q < 2 ^ (k + 1)) && q.testBit k) := by
    intro q
    rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hq : q < 2 ^ (k + 1)
    · by_cases hq' : 2 ^ k ≤ q
      · have h3 : q - 2 ^ k < 2 ^ k := by omega
        have h4 := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hq' hq
        simp [hq, hq', h3, h4]
      · have h4 := Nat.testBit_lt_two_pow (Nat.lt_of_not_le hq')
        have h5 : ¬ q ≥ 2 ^ k := hq'
        simp [hq, h5, h4]
    · have h3 : ¬ q - 2 ^ k < 2 ^ k := by omega
      simp [hq, h3]
  rw [Nat.sub_eq, dbl_bits (23 - k) (2 ^ (k + 1)) _ (dvd_refl _) h0 q, ← pow_add,
    show k + 1 + (23 - k) = 24 by omega]

theorem mapRevK_eq {α : Sort*} (f : ℕ → ℕ) :
    ∀ (xs acc : List ℕ) (k : List ℕ → α), mapRevK f xs acc k = k ((xs.map f).reverse ++ acc)
  | [], acc, k => rfl
  | x :: xs, acc, k => by
    change strict (f x) (fun y => mapRevK f xs (y :: acc) k) = _
    rw [strict_eq, mapRevK_eq f xs]
    simp

noncomputable def pms24 : List ℕ := (List.range' 0 24).map pmask

theorem withPms_eq {α : Sort*} (k : List ℕ → α) : withPms k = k pms24 := by
  unfold withPms
  rw [mapRevK_eq, List.map_reverse, List.reverse_reverse, List.append_nil]
  rfl

theorem xorSel_cons (P : ℕ) (pms : List ℕ) (a acc : ℕ) :
    xorSel (P :: pms) a acc = xorSel pms (a / 2) (if a.testBit 0 = true then acc ^^^ P else acc) := by
  change xorSel pms (a / 2) (Bool.rec (motive := fun _ => ℕ) acc (acc ^^^ P) (Nat.beq (a % 2) 1))
    = _
  rw [beq_mod2]
  cases a.testBit 0 <;> rfl

theorem xorSel_bits : ∀ (L k a acc p : ℕ), k + L ≤ 24 →
    (xorSel ((List.range' k L).map pmask) a acc).testBit p =
      (acc.testBit p ^^ (decide (p < 2 ^ 24) && par L (a &&& (p >>> k))))
  | 0, k, a, acc, p, _ => by
    change acc.testBit p = _
    rw [show par 0 (a &&& (p >>> k)) = false from rfl]
    simp
  | L + 1, k, a, acc, p, hk => by
    rw [List.range'_succ, List.map_cons, xorSel_cons, xorSel_bits L (k + 1) _ _ p (by omega),
      par_and_shift]
    have hpm := pmask_bits (show k < 24 by omega) p
    cases ha : a.testBit 0
    · simp only [Bool.false_eq_true, if_false, Bool.false_and, Bool.false_xor]
    · simp only [if_true, Nat.testBit_xor, hpm, Bool.true_and]
      cases acc.testBit p <;> cases decide (p < 2 ^ 24) <;> cases p.testBit k <;>
        cases par L (a / 2 &&& (p >>> (k + 1))) <;> rfl

theorem opMask_bits {o : ℕ × ℕ} (hi : o.1 < 24) (p : ℕ) :
    (opMask pms24 o).testBit p = (decide (p < 2 ^ 24) && par 24 (o.2 &&& p) && !p.testBit o.1) := by
  unfold opMask pms24
  rw [strict_eq]
  have hg : ((List.range' 0 24).map pmask).getD o.1 0 = pmask o.1 := by
    simp [List.getD_eq_getElem?_getD, hi]
  simp only [hg, Nat.xor_eq, Nat.land_eq, Nat.testBit_xor, Nat.testBit_and,
    xorSel_bits 24 0 o.2 0 p (by omega), pmask_bits hi, Nat.zero_testBit, Nat.shiftRight_zero]
  cases decide (p < 2 ^ 24) <;> cases par 24 (o.2 &&& p) <;> cases p.testBit o.1 <;> rfl

theorem prepK_eq {α : Sort*} (pms : List ℕ) :
    ∀ (ops acc : List (ℕ × ℕ)) (k : List (ℕ × ℕ) → α),
      prepK pms ops acc k = k ((ops.map fun o => (1 <<< o.1, opMask pms o)).reverse ++ acc)
  | [], acc, k => rfl
  | o :: ops, acc, k => by
    change strict (opMask pms o) (fun m => strict (1 <<< o.1) fun s =>
      prepK pms ops ((s, m) :: acc) k) = _
    rw [strict_eq, strict_eq, prepK_eq pms ops]
    simp

noncomputable def stp (o : ℕ × ℕ) : ℕ × ℕ := (1 <<< o.1, opMask pms24 o)

theorem withPrep_eq {α : Sort*} (ops : List (ℕ × ℕ)) (k : List (ℕ × ℕ) → α) :
    withPrep pms24 ops k = k (ops.map stp) := by
  unfold withPrep
  rw [prepK_eq, List.map_reverse, List.reverse_reverse, List.append_nil]
  rfl

theorem swp_bits {o : ℕ × ℕ} (ho : OK o) {m : ℕ}
    (hm : ∀ p, m.testBit p = (decide (p < 2 ^ 24) && par 24 (o.2 &&& p) && !p.testBit o.1))
    (S q : ℕ) :
    (swp (1 <<< o.1) m S).testBit q =
      if q < 2 ^ 24 then S.testBit (opApp o q) else S.testBit q := by
  obtain ⟨hi, ha⟩ := ho
  change (S ^^^ (((S ^^^ (S >>> (1 <<< o.1))) &&& m) ^^^
    (((S ^^^ (S >>> (1 <<< o.1))) &&& m) <<< (1 <<< o.1)))).testBit q = _
  rw [Nat.one_shiftLeft, opApp_eq]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, hm]
  cases hqi : q.testBit o.1
  · rw [xor_clear hqi]
    have hsh : (decide (q ≥ 2 ^ o.1) && ((S.testBit (q - 2 ^ o.1) ^^
        S.testBit (2 ^ o.1 + (q - 2 ^ o.1))) && (decide (q - 2 ^ o.1 < 2 ^ 24) &&
        par 24 (o.2 &&& (q - 2 ^ o.1)) && !(q - 2 ^ o.1).testBit o.1))) = false := by
      by_cases hge : 2 ^ o.1 ≤ q
      · simp [clear_sub hqi hge]
      · simp [hge]
    rw [hsh, Bool.xor_false, Nat.add_comm (2 ^ o.1) q]
    by_cases hq : q < 2 ^ 24 <;> cases hp : par 24 (o.2 &&& q) <;>
      simp [-Nat.reducePow, hq, hp] <;>
      cases S.testBit q <;> cases S.testBit (q + 2 ^ o.1) <;> rfl
  · have hge := Nat.ge_two_pow_of_testBit hqi
    rw [xor_set hqi, ← xor_set hqi, and_xor_clear ha, xor_set hqi, set_sub hqi,
      show 2 ^ o.1 + (q - 2 ^ o.1) = q by omega,
      show decide (q - 2 ^ o.1 < 2 ^ 24) = decide (q < 2 ^ 24) from
        decide_eq_decide.2 (sub_lt_iff hi hqi)]
    by_cases hq : q < 2 ^ 24 <;> cases hp : par 24 (o.2 &&& q) <;>
      simp [-Nat.reducePow, hq, hp, hge] <;>
      cases S.testBit q <;> cases S.testBit (q - 2 ^ o.1) <;> rfl

theorem img_bits {ops : List (ℕ × ℕ)} (hok : ∀ o ∈ ops, OK o) :
    ∀ S q, (img (ops.map stp) S).testBit q =
      if q < 2 ^ 24 then S.testBit (opsApp ops q) else S.testBit q := by
  induction ops with
  | nil => intro S q; change S.testBit q = _; split_ifs <;> rfl
  | cons o ops ih =>
    intro S q
    have ho := hok o (List.mem_cons_self ..)
    change (img (ops.map stp) (swp (1 <<< o.1) (opMask pms24 o) S)).testBit q = _
    rw [ih (fun o' h => hok o' (List.mem_cons_of_mem _ h))]
    split_ifs with hq
    · rw [swp_bits ho (opMask_bits ho.1), if_pos (opsApp_lt (fun o' h =>
        hok o' (List.mem_cons_of_mem _ h)) hq), opsApp_cons]
    · rw [swp_bits ho (opMask_bits ho.1), if_neg hq]

theorem img_lt {ops : List (ℕ × ℕ)} (hok : ∀ o ∈ ops, OK o) {S : ℕ} (hS : S < 2 ^ 2 ^ 24) :
    img (ops.map stp) S < 2 ^ 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro q hq
  rw [img_bits hok, if_neg (by
    have : (24 : ℕ) < 2 ^ 24 := by norm_num
    have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) this
    omega)]
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by norm_num) hq))

theorem iterK_inv {P Q : List (ℕ × ℕ)} (I : ℕ → Prop) (hI : ∀ S, I S → I (round P Q S)) :
    ∀ (r S : ℕ) (k : ℕ → Bool), I S → iterK P Q r S k = true → ∃ S', I S' ∧ k S' = true
  | 0, S, k, hS, h => ⟨S, hS, h⟩
  | r + 1, S, k, hS, h => by
    have e : iterK P Q (r + 1) S k = strict (round P Q S) (fun S' => iterK P Q r S' k) := rfl
    have h' : iterK P Q r (round P Q S) k = true := by
      rw [e, strict_eq] at h
      exact h
    exact iterK_inv I hI r _ k (hI S hS) h'

def Inv (F G : ℕ → ℕ) (root S : ℕ) : Prop :=
  S < 2 ^ 2 ^ 24 ∧ S.testBit root = true ∧ ∀ q < 2 ^ 24, S.testBit q = true → Back F G root q

theorem round_inv {opsP opsQ : List (ℕ × ℕ)} {F G : ℕ → ℕ} {root : ℕ}
    (hPok : ∀ o ∈ opsP, OK o) (hQok : ∀ o ∈ opsQ, OK o)
    (hF : ∀ v < 2 ^ 24, opsApp opsP v = F v) (hG : ∀ v < 2 ^ 24, opsApp opsQ v = G v)
    (S : ℕ) (hS : Inv F G root S) : Inv F G root (round (opsP.map stp) (opsQ.map stp) S) := by
  obtain ⟨hlt, hr, hb⟩ := hS
  change Inv F G root (S ||| (img (opsP.map stp) S ||| img (opsQ.map stp) S))
  refine ⟨Nat.or_lt_two_pow hlt (Nat.or_lt_two_pow (img_lt hPok hlt) (img_lt hQok hlt)), ?_, ?_⟩
  · simp [hr]
  · intro q hq h
    rw [Nat.testBit_or, Nat.testBit_or, img_bits hPok, img_bits hQok, if_pos hq, if_pos hq] at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact hb q hq h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · have := hb _ (opsApp_lt hPok hq) h
      rw [hF q hq] at this
      exact Back.sf this
    · have := hb _ (opsApp_lt hQok hq) h
      rw [hG q hq] at this
      exact Back.sg this

def D (w : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | M + 1 => f 0 + 2 ^ w * D w (fun j => f (j + 1)) M

theorem testBit_D {w : ℕ} (hw : 0 < w) :
    ∀ (M : ℕ) (f : ℕ → ℕ), (∀ j < M, f j < 2 ^ w) →
      ∀ q, (D w f M).testBit q = (decide (q / w < M) && (f (q / w)).testBit (q % w))
  | 0, f, _, q => by simp [D]
  | M + 1, f, hf, q => by
    rw [D, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (hf 0 (by omega))]
    split_ifs with hq
    · rw [Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq]
      simp
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + w := ⟨q - w, by omega⟩
      rw [Nat.add_sub_cancel, testBit_D hw M _ (fun j hj => hf (j + 1) (by omega)),
        Nat.add_div_right _ hw, Nat.add_mod_right]
      simp

theorem D_add (w : ℕ) : ∀ (M : ℕ) (f g : ℕ → ℕ),
    D w (fun j => f j + g j) M = D w f M + D w g M
  | 0, f, g => rfl
  | M + 1, f, g => by
    simp only [D]
    rw [D_add w M (fun j => f (j + 1)) (fun j => g (j + 1))]
    ring

theorem D_pair (w : ℕ) : ∀ (M : ℕ) (f : ℕ → ℕ),
    D w (fun j => if j % 2 = 0 then f (j / 2) else 0) (2 * M) = D (2 * w) f M
  | 0, f => rfl
  | M + 1, f => by
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring]
    simp only [D]
    have h : (fun j => if (j + 1 + 1) % 2 = 0 then f ((j + 1 + 1) / 2) else 0) =
        (fun j => if j % 2 = 0 then f (j / 2 + 1) else 0) := by
      funext j
      rw [Nat.add_assoc, Nat.add_mod_right, Nat.add_div_right _ (by norm_num)]
    simp only [Nat.zero_mod, Nat.zero_div, if_true, show (0 + 1) % 2 = 1 from rfl,
      show (1 : ℕ) ≠ 0 from one_ne_zero, if_false, Nat.zero_add]
    rw [h, D_pair w M (fun j => f (j + 1)), two_mul w, pow_add]
    ring

noncomputable def cnt (S k j : ℕ) : ℕ :=
  ((Finset.range (2 ^ 24)).filter (fun p => S.testBit p = true ∧ p / 2 ^ k = j)).card

theorem cnt_succ (S k J : ℕ) : cnt S (k + 1) J = cnt S k (2 * J) + cnt S k (2 * J + 1) := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint, ← Finset.filter_or]
  · apply congrArg Finset.card
    apply Finset.filter_congr
    intro p _
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    have key : ∀ x, x / 2 = J ↔ x = 2 * J ∨ x = 2 * J + 1 := by intro x; omega
    rw [key]
    exact and_or_left
  · rw [Finset.disjoint_filter]
    intro p _ h1 h2
    omega

theorem cnt_lt (S k j : ℕ) : cnt S k j < 2 ^ 2 ^ k := by
  calc cnt S k j ≤ (Finset.Ico (2 ^ k * j) (2 ^ k * j + 2 ^ k)).card := by
        unfold cnt
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
        obtain ⟨_, _, hpj⟩ := hp
        have h1 := Nat.div_add_mod p (2 ^ k)
        have h2 := Nat.mod_lt p (Nat.two_pow_pos k)
        rw [hpj] at h1
        generalize 2 ^ k * j = a at h1 ⊢
        generalize 2 ^ k = b at h1 h2 ⊢
        omega
    _ = 2 ^ k := by simp
    _ < 2 ^ 2 ^ k := Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self

theorem cnt_init {S : ℕ} (hS : S < 2 ^ 2 ^ 24) : S = D (2 ^ 0) (cnt S 0) (2 ^ (24 - 0)) := by
  rw [pow_zero, Nat.sub_zero]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_D one_pos _ _ (fun j _ => by simpa using cnt_lt S 0 j), Nat.div_one, Nat.mod_one]
  have hc : cnt S 0 q = if q < 2 ^ 24 ∧ S.testBit q = true then 1 else 0 := by
    unfold cnt
    simp only [pow_zero, Nat.div_one]
    split_ifs with h
    · rw [Finset.card_eq_one]
      refine ⟨q, ?_⟩
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨_, _, rfl⟩
        rfl
      · rintro rfl
        exact ⟨h.1, h.2, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p hp ⟨hs, rfl⟩
      exact h ⟨Finset.mem_range.1 hp, hs⟩
  rw [hc]
  by_cases hq : q < 2 ^ 24
  · cases hs : S.testBit q <;> simp [-Nat.reducePow, hq, hs]
  · have : S.testBit q = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [-Nat.reducePow, hq, this]

noncomputable def popG (M : ℕ) (pms : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ c => c)
    (fun P _ ih w c => strict (Nat.xor M P) fun Q =>
      strict (Nat.add (Nat.land c Q) (Nat.land (Nat.shiftRight c w) Q)) (ih (Nat.mul 2 w))) pms

theorem popAux_eq_popG :
    ∃ M : ℕ, (∀ q, M.testBit q = decide (q < 2 ^ 24)) ∧
      ∀ pms w c, popAux pms w c = popG M pms w c := by
  refine ⟨_, ?_, fun pms w c => rfl⟩
  intro q
  rw [Nat.testBit_two_pow_sub_one, show W = 2 ^ 24 by norm_num [W]]

theorem popG_cons (M P : ℕ) (pms : List ℕ) (w c : ℕ) :
    popG M (P :: pms) w c = popG M pms (2 * w) ((c &&& (M ^^^ P)) + ((c >>> w) &&& (M ^^^ P))) := by
  change strict (Nat.xor M P) (fun Q => strict (Nat.add (Nat.land c Q)
    (Nat.land (Nat.shiftRight c w) Q)) (popG M pms (Nat.mul 2 w))) = _
  rw [strict_eq, strict_eq]
  rfl

theorem pop_step {M S k : ℕ} (hM : ∀ q, M.testBit q = decide (q < 2 ^ 24)) (hk : k < 24) (c : ℕ)
    (hc : c = D (2 ^ k) (cnt S k) (2 * 2 ^ (23 - k))) :
    (c &&& (M ^^^ pmask k)) + ((c >>> 2 ^ k) &&& (M ^^^ pmask k)) =
      D (2 ^ (k + 1)) (cnt S (k + 1)) (2 ^ (23 - k)) := by
  have hw : 0 < 2 ^ k := Nat.two_pow_pos k
  have hNw : 2 * 2 ^ (23 - k) * 2 ^ k = 2 ^ 24 := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hQ : ∀ q, (M ^^^ pmask k).testBit q =
      (decide (q / 2 ^ k < 2 * 2 ^ (23 - k)) && !decide (q / 2 ^ k % 2 = 1)) := by
    intro q
    rw [Nat.testBit_xor, hM, pmask_bits hk, Nat.testBit_eq_decide_div_mod_eq (i := k)]
    have h1 : q / 2 ^ k < 2 * 2 ^ (23 - k) ↔ q < 2 ^ 24 := by
      rw [Nat.div_lt_iff_lt_mul hw, hNw]
    by_cases hq : q < 2 ^ 24
    · cases hb : decide (q / 2 ^ k % 2 = 1) <;> simp [-Nat.reducePow, hq, h1.2 hq, hb]
    · have : ¬ q / 2 ^ k < 2 * 2 ^ (23 - k) := fun h => hq (h1.1 h)
      simp [-Nat.reducePow, hq, this]
  have hbd : ∀ j < 2 * 2 ^ (23 - k), cnt S k j < 2 ^ 2 ^ k := fun j _ => cnt_lt S k j
  have hbd1 : ∀ j < 2 * 2 ^ (23 - k), (if j % 2 = 0 then cnt S k j else 0) < 2 ^ 2 ^ k := by
    intro j _
    split_ifs
    · exact cnt_lt S k j
    · exact Nat.two_pow_pos _
  have hbd2 : ∀ j < 2 * 2 ^ (23 - k), (if j % 2 = 0 then cnt S k (j + 1) else 0) < 2 ^ 2 ^ k := by
    intro j _
    split_ifs
    · exact cnt_lt S k (j + 1)
    · exact Nat.two_pow_pos _
  have e1 : c &&& (M ^^^ pmask k) =
      D (2 ^ k) (fun j => if j % 2 = 0 then cnt S k j else 0) (2 * 2 ^ (23 - k)) := by
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_and, hc, testBit_D hw _ _ hbd, testBit_D hw _ _ hbd1, hQ]
    by_cases h1 : q / 2 ^ k < 2 * 2 ^ (23 - k) <;>
      rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ k) with h2 | h2 <;> simp [h1, h2]
  have e2 : (c >>> 2 ^ k) &&& (M ^^^ pmask k) =
      D (2 ^ k) (fun j => if j % 2 = 0 then cnt S k (j + 1) else 0) (2 * 2 ^ (23 - k)) := by
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_and, Nat.testBit_shiftRight, hc, testBit_D hw _ _ hbd,
      testBit_D hw _ _ hbd2, hQ, Nat.add_comm (2 ^ k) q, Nat.add_div_right _ hw,
      Nat.add_mod_right]
    by_cases h1 : q / 2 ^ k < 2 * 2 ^ (23 - k) <;>
      rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ k) with h2 | h2
    · have h3 : q / 2 ^ k + 1 < 2 * 2 ^ (23 - k) := by omega
      simp [h1, h2, h3]
    all_goals simp [h1, h2]
  rw [e1, e2, ← D_add]
  have e3 : (fun j => (if j % 2 = 0 then cnt S k j else 0) +
      (if j % 2 = 0 then cnt S k (j + 1) else 0)) =
      (fun j => if j % 2 = 0 then cnt S (k + 1) (j / 2) else 0) := by
    funext j
    split_ifs with h
    · rw [cnt_succ, show 2 * (j / 2) = j by omega]
    · rfl
  rw [e3, D_pair, show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, Nat.mul_comm]]

theorem D_one (w : ℕ) (f : ℕ → ℕ) : D w f 1 = f 0 := by
  simp [D]

theorem popG_eq {M S : ℕ} (hM : ∀ q, M.testBit q = decide (q < 2 ^ 24)) :
    ∀ (L k c : ℕ), k + L = 24 → c = D (2 ^ k) (cnt S k) (2 ^ (24 - k)) →
      popG M ((List.range' k L).map pmask) (2 ^ k) c = cnt S 24 0
  | 0, k, c, hk, hc => by
    obtain rfl : k = 24 := by omega
    change c = _
    rw [hc, Nat.sub_self, pow_zero, D_one]
  | L + 1, k, c, hk, hc => by
    rw [List.range'_succ, List.map_cons, popG_cons, ← pow_succ']
    refine popG_eq hM L (k + 1) _ (by omega) ?_
    rw [pop_step hM (by omega) c (by rw [hc, show 24 - k = 23 - k + 1 by omega, pow_succ']),
      show 24 - (k + 1) = 23 - k by omega]

theorem popc_eq {S : ℕ} (hS : S < 2 ^ 2 ^ 24) :
    popc pms24 S = ((Finset.range (2 ^ 24)).filter (fun v => S.testBit v = true)).card := by
  obtain ⟨M, hM, hpop⟩ := popAux_eq_popG
  have h := popG_eq hM 24 0 S (by omega) (cnt_init hS)
  rw [pow_zero] at h
  change popAux pms24 1 S = _
  rw [hpop, pms24, h]
  unfold cnt
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p hp
  rw [Nat.div_eq_of_lt (Finset.mem_range.1 hp)]
  exact and_iff_left rfl

theorem closed_of_preimage {φ : ℕ → ℕ} {M : ℕ} (hinj : Function.Injective φ)
    (hlt : ∀ q < M, φ q < M) {T : Finset ℕ} (hT : ∀ v ∈ T, v < M)
    (hpre : ∀ q < M, φ q ∈ T → q ∈ T) : ∀ v ∈ T, φ v ∈ T := by
  have hR : (Finset.range M).image φ = Finset.range M := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hlt q (Finset.mem_range.1 hq))
    · rw [Finset.card_image_of_injective _ hinj]
  have hsub : T ⊆ T.image φ := by
    intro t ht
    have : t ∈ (Finset.range M).image φ := by
      rw [hR]
      exact Finset.mem_range.2 (hT t ht)
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 this
    exact Finset.mem_image_of_mem φ (hpre q (Finset.mem_range.1 hq) ht)
  have heq : T = T.image φ :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ hinj])
  intro v hv
  rw [heq]
  exact Finset.mem_image_of_mem φ hv

theorem orbOK_sound {cP cQ : List ℕ} {opsP opsQ : List (ℕ × ℕ)} {root n steps : ℕ}
    (h : orbOK cP cQ opsP opsQ root n steps = true) :
    ∃ T : Finset ℕ, (∀ v ∈ T, v < 2 ^ 24) ∧ root ∈ T ∧
      (∀ v ∈ T, vecMulN 24 cP.toArray v ∈ T ∧ vecMulN 24 cQ.toArray v ∈ T) ∧
      (∀ v ∈ T, Back (vecMulN 24 cP.toArray) (vecMulN 24 cQ.toArray) root v) ∧
      T.card = n ∧ ∀ v ∈ T, root ≤ v := by
  have hW : W = 2 ^ 24 := by norm_num [W]
  unfold orbOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨hP, hQ⟩, hroot⟩, h⟩ := h
  rw [hW] at hroot
  rw [withPms_eq, withPrep_eq, withPrep_eq] at h
  obtain ⟨hPok, hPF⟩ := opsOK_facts hP
  obtain ⟨hQok, hQF⟩ := opsOK_facts hQ
  have hinit : Inv (vecMulN 24 cP.toArray) (vecMulN 24 cQ.toArray) root (1 <<< root) := by
    rw [Nat.one_shiftLeft]
    refine ⟨Nat.pow_lt_pow_right (by norm_num) hroot, Nat.testBit_two_pow_self, ?_⟩
    intro q _ hq
    rw [Nat.testBit_two_pow, decide_eq_true_eq] at hq
    subst hq
    exact Back.base
  obtain ⟨S, ⟨hSlt, hSr, hSb⟩, hfin⟩ := iterK_inv _
    (fun S hS => round_inv hPok hQok hPF hQF S hS) steps _ _ hinit h
  have hfin' : (Nat.beq (round (opsP.map stp) (opsQ.map stp) S) S &&
      Nat.beq (S &&& (2 ^ root - 1)) 0 && Nat.beq (popc pms24 S) n) = true := hfin
  simp only [Bool.and_eq_true, Nat.beq_eq] at hfin'
  obtain ⟨⟨hcl, hlow⟩, hpop⟩ := hfin'
  let T := (Finset.range (2 ^ 24)).filter (fun v => S.testBit v = true)
  have hmem : ∀ v, v ∈ T ↔ v < 2 ^ 24 ∧ S.testBit v = true := fun v => by simp [T]
  have hTlt : ∀ v ∈ T, v < 2 ^ 24 := fun v hv => ((hmem v).1 hv).1
  have hround : ∀ q < 2 ^ 24,
      (S.testBit q || (S.testBit (opsApp opsP q) || S.testBit (opsApp opsQ q))) = S.testBit q := by
    intro q hq
    have := congrArg (fun x => x.testBit q) hcl
    change (S ||| (img (opsP.map stp) S ||| img (opsQ.map stp) S)).testBit q = S.testBit q at this
    rwa [Nat.testBit_or, Nat.testBit_or, img_bits hPok, img_bits hQok, if_pos hq, if_pos hq] at this
  have hpreP : ∀ q < 2 ^ 24, opsApp opsP q ∈ T → q ∈ T := by
    intro q hq h
    rw [hmem] at h ⊢
    refine ⟨hq, ?_⟩
    rw [← hround q hq, h.2]
    simp
  have hpreQ : ∀ q < 2 ^ 24, opsApp opsQ q ∈ T → q ∈ T := by
    intro q hq h
    rw [hmem] at h ⊢
    refine ⟨hq, ?_⟩
    rw [← hround q hq, h.2]
    simp
  have hclP := closed_of_preimage (opsApp_inj hPok) (fun q hq => opsApp_lt hPok hq) hTlt hpreP
  have hclQ := closed_of_preimage (opsApp_inj hQok) (fun q hq => opsApp_lt hQok hq) hTlt hpreQ
  refine ⟨T, hTlt, (hmem root).2 ⟨hroot, hSr⟩, fun v hv => ?_,
    fun v hv => hSb v (hTlt v hv) ((hmem v).1 hv).2, ?_, ?_⟩
  · rw [← hPF v (hTlt v hv), ← hQF v (hTlt v hv)]
    exact ⟨hclP v hv, hclQ v hv⟩
  · rw [← hpop, popc_eq hSlt]
  · intro v hv
    by_contra! hlt
    have := congrArg (fun x => x.testBit v) hlow
    simp [Nat.testBit_and, ((hmem v).1 hv).2, hlt] at this

theorem back_mem {P Q : GL24} {cP cQ : Array ℕ} (hP : ActsBy P cP) (hQ : ActsBy Q cQ)
    {root v : ℕ} (hb : Back (vecMulN 24 cP) (vecMulN 24 cQ) root v) :
    toVecD 24 v ∈ kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) := by
  have hPm : P ∈ Subgroup.closure {P, Q} := Subgroup.subset_closure (Set.mem_insert _ _)
  have hQm : Q ∈ Subgroup.closure {P, Q} :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  induction hb with
  | base => exact mem_kOrbit_self _ _
  | @sf v _ ih =>
    rw [← kOrbit_eq_of_mem ih]
    refine ⟨P⁻¹, Subgroup.inv_mem _ hPm, ?_⟩
    rw [← hP, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  | @sg v _ ih =>
    rw [← kOrbit_eq_of_mem ih]
    refine ⟨Q⁻¹, Subgroup.inv_mem _ hQm, ?_⟩
    rw [← hQ, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem orbit_of_orbOK {P Q : GL24} {cP cQ : List ℕ} {opsP opsQ : List (ℕ × ℕ)}
    {root n steps : ℕ} (hP : ActsBy P cP.toArray) (hQ : ActsBy Q cQ.toArray)
    (h : orbOK cP cQ opsP opsQ root n steps = true) :
    (kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root)).ncard = n ∧
      ∀ c < 2 ^ 24, toVecD 24 c ∈ kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) →
        root ≤ c := by
  obtain ⟨T, hlt, hr, hcl, hback, hcard, hmin⟩ := orbOK_sound h
  have hset : kOrbit (Subgroup.closure {P, Q}) (toVecD 24 root) =
      toVecD 24 '' (T : Set ℕ) := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      refine closure_mapsTo ((T.finite_toSet).image _) ?_ ?_ hk _ ⟨root, hr, rfl⟩
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨_, (hcl v hv).1, (hP v).symm⟩
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨_, (hcl v hv).2, (hQ v).symm⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact back_mem hP hQ (hback v hv)
  refine ⟨?_, fun c hc hmem => ?_⟩
  · rw [hset, Set.InjOn.ncard_image fun a ha b hb hab => toVecD_injective (hlt a ha) (hlt b hb) hab,
      Set.ncard_coe_finset, hcard]
  · rw [hset] at hmem
    obtain ⟨v, hv, hvc⟩ := hmem
    rw [← toVecD_injective (hlt v hv) hc hvc]
    exact hmin v hv

end CFSG.KS.F2Set24

end
