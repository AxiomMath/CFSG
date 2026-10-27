module

public import Certificates.Data.Kernel.LocalQT.PermW
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Fintype.BigOperators

public section

namespace CFSG.KC.LQT.PW

open Finset

theorem imgW_eq (w s i : ℕ) : imgW w s i = (s >>> (w * i)) &&& (2 ^ w - 1) := by
  have e : Nat.shiftLeft 1 w = 2 ^ w := by
    change 1 <<< w = 2 ^ w
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [imgW, e]
  rfl

theorem imgW_div (w s i : ℕ) : imgW w s i = s / 2 ^ (w * i) % 2 ^ w := by
  rw [imgW_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem testBit_imgW (w s i j : ℕ) :
    (imgW w s i).testBit j = (decide (j < w) && s.testBit (w * i + j)) := by
  rw [imgW_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem imgW_lt (w s i : ℕ) : imgW w s i < 2 ^ w := by
  rw [imgW_div]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem eq_of_imgW {w : ℕ} (hw : 0 < w) {s t : ℕ} (h : ∀ i, imgW w s i = imgW w t i) : s = t := by
  apply Nat.eq_of_testBit_eq
  intro b
  have e : w * (b / w) + b % w = b := Nat.div_add_mod b w
  have hb : b % w < w := Nat.mod_lt b hw
  have h1 : s.testBit b = (imgW w s (b / w)).testBit (b % w) := by
    rw [testBit_imgW, e]
    simp [hb]
  have h2 : t.testBit b = (imgW w t (b / w)).testBit (b % w) := by
    rw [testBit_imgW, e]
    simp [hb]
  rw [h1, h2, h]

theorem pos_of_bit {w a k q pj : ℕ} (ha : a < 2 ^ w) (hq : q < w) (hle : w * pj ≤ w * k + q)
    (hb : a.testBit (w * k + q - w * pj) = true) : pj = k ∧ a.testBit q = true := by
  have hlt : w * k + q - w * pj < w := by
    apply Nat.lt_of_not_le
    intro hc
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hc))]
      at hb
    exact absurd hb (by decide)
  have hjk : pj = k := by
    rcases Nat.lt_trichotomy pj k with h | h | h
    · have h' : w * (pj + 1) ≤ w * k := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h'
      omega
    · exact h
    · have h' : w * (k + 1) ≤ w * pj := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h'
      omega
  subst hjk
  have e : w * pj + q - w * pj = q := by omega
  exact ⟨rfl, by rwa [e] at hb⟩

@[expose] def sumW (w : ℕ) (f : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ range m, f i * 2 ^ (w * i)

theorem sumW_succ (w : ℕ) (f : ℕ → ℕ) (m : ℕ) :
    sumW w f (m + 1) = sumW w f m + f m * 2 ^ (w * m) := by
  rw [sumW, sum_range_succ, ← sumW]

theorem sumW_congr {w : ℕ} {f g : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i = g i) :
    sumW w f m = sumW w g m :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

theorem sumW_lt {w : ℕ} {f : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i < 2 ^ w) :
    sumW w f m < 2 ^ (w * m) := by
  induction m with
  | zero => simp [sumW]
  | succ m ih =>
    rw [sumW_succ, Nat.mul_succ, pow_add]
    have h1 := ih fun i hi => h i (by omega)
    have hle : (f m + 1) * 2 ^ (w * m) ≤ 2 ^ w * 2 ^ (w * m) :=
      Nat.mul_le_mul_right _ (h m (by omega))
    calc sumW w f m + f m * 2 ^ (w * m) < 2 ^ (w * m) + f m * 2 ^ (w * m) :=
          Nat.add_lt_add_right h1 _
      _ = (f m + 1) * 2 ^ (w * m) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * m) := hle
      _ = 2 ^ (w * m) * 2 ^ w := Nat.mul_comm _ _

theorem sumW_digit {w : ℕ} {f : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i < 2 ^ w) {j : ℕ} (hj : j < m) :
    sumW w f m / 2 ^ (w * j) % 2 ^ w = f j := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [sumW_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 + j := ⟨m - j - 1, by omega⟩
      have e : f m * 2 ^ (w * m) = (f m * 2 ^ (w * k)) * 2 ^ w * 2 ^ (w * j) := by
        rw [hk]
        ring
      rw [e, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]
      exact ih (fun i hi => h i (by omega)) hj
    · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (sumW_lt fun i hi => h i (by omega)), Nat.zero_add]
      exact Nat.mod_eq_of_lt (h _ (by omega))

theorem imgW_sumW {w : ℕ} {f : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i < 2 ^ w) (j : ℕ) :
    imgW w (sumW w f m) j = if j < m then f j else 0 := by
  rw [imgW_div]
  split_ifs with hj
  · exact sumW_digit h hj
  · have hlt : sumW w f m < 2 ^ (w * j) := Nat.lt_of_lt_of_le (sumW_lt h)
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w (by omega)))
    rw [Nat.div_eq_of_lt hlt]
    rfl

@[expose] def orW (w : ℕ) (v p : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (v i) (Nat.mul w (p i)))) m

theorem testBit_orW (w : ℕ) (v p : ℕ → ℕ) (b : ℕ) : ∀ m,
    (orW w v p m).testBit b =
      (List.range m).any fun i => decide (w * p i ≤ b) && (v i).testBit (b - w * p i)
  | 0 => by
    change (0 : ℕ).testBit b = _
    simp
  | m + 1 => by
    have e : orW w v p (m + 1) = orW w v p m ||| (v m <<< (w * p m)) := rfl
    rw [e, Nat.testBit_or, testBit_orW w v p b m, List.range_succ, List.any_append,
      Nat.testBit_shiftLeft]
    simp

theorem imgW_orW_of {w : ℕ} {v p : ℕ → ℕ} {m : ℕ} (hv : ∀ i < m, v i < 2 ^ w)
    (hp : ∀ i < m, ∀ j < m, p i = p j → i = j) {i k : ℕ} (hi : i < m) (hk : p i = k) :
    imgW w (orW w v p m) k = v i := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_imgW, testBit_orW]
  by_cases hq : q < w
  · simp only [hq, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, hle, hb⟩
      obtain ⟨hjk, hb⟩ := pos_of_bit (hv j hj) hq hle hb
      rwa [hp j hj i hi (hjk.trans hk.symm)] at hb
    · intro hb
      refine ⟨i, hi, by rw [hk]; omega, ?_⟩
      have e : w * k + q - w * p i = q := by rw [hk]; omega
      rwa [e]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hv i hi)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hq]

theorem imgW_orW_none {w : ℕ} {v p : ℕ → ℕ} {m : ℕ} (hv : ∀ i < m, v i < 2 ^ w) {k : ℕ}
    (hk : ∀ i < m, p i ≠ k) : imgW w (orW w v p m) k = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_imgW, testBit_orW, Nat.zero_testBit]
  by_cases hq : q < w
  · simp only [hq, decide_true, Bool.true_and]
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨j, hj, hb⟩ := List.any_eq_true.1 h
    rw [List.mem_range] at hj
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact hk j hj (pos_of_bit (hv j hj) hq hb.1 hb.2).1
  · simp [hq]

theorem ofFnW_eq (n w : ℕ) (g : ℕ → ℕ) : ofFnW n w g = orW w g (fun i => i) n := rfl

theorem invW_eq (n w s : ℕ) : invW n w s = orW w (fun i => i) (imgW w s) n := rfl

@[expose] def arrAux (w : ℕ) (t : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 0)
    (fun x _ ih k => Nat.lor (Nat.shiftLeft x (Nat.mul w k)) (ih (Nat.succ k))) t

theorem arrCodeW_eq (w : ℕ) (t : List ℕ) : arrCodeW w t = arrAux w t 0 := rfl

theorem testBit_arrAux (w b : ℕ) : ∀ (t : List ℕ) (s : ℕ),
    (arrAux w t s).testBit b = (List.range t.length).any fun j =>
      decide (w * (s + j) ≤ b) && (t.getD j 0).testBit (b - w * (s + j))
  | [], s => by
    change (0 : ℕ).testBit b = _
    simp
  | x :: t, s => by
    have e : arrAux w (x :: t) s = (x <<< (w * s)) ||| arrAux w t (s + 1) := rfl
    rw [e, Nat.testBit_or, testBit_arrAux w b t (s + 1), Nat.testBit_shiftLeft, List.length_cons,
      List.range_succ_eq_map, List.any_cons, List.any_map]
    have e2 : ∀ j, s + 1 + j = s + (j + 1) := fun j => by omega
    simp [Function.comp_def, e2]

theorem arrCodeW_eq_orW (w : ℕ) (t : List ℕ) :
    arrCodeW w t = orW w (fun j => t.getD j 0) (fun j => j) t.length := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [arrCodeW_eq, testBit_arrAux, testBit_orW]
  simp

theorem imgW_arrCodeW {w : ℕ} {t : List ℕ} (ht : ∀ x ∈ t, x < 2 ^ w) (k : ℕ) :
    imgW w (arrCodeW w t) k = t.getD k 0 := by
  have hv : ∀ i < t.length, t.getD i 0 < 2 ^ w := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact ht _ (List.getElem_mem hi)
  rw [arrCodeW_eq_orW]
  by_cases hk : k < t.length
  · exact imgW_orW_of hv (fun i _ j _ h => h) hk rfl
  · rw [imgW_orW_none hv (fun i hi h => hk (by omega)), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), Option.getD_none]

theorem horner (n : ℕ) (f : ℕ → ℕ) : ∀ m, m ≤ n →
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc * n + f (n - 1 - k)) m =
      Nat.ofDigits n ((List.range m).map fun j => f (n - m + j))
  | 0, _ => rfl
  | m + 1, hm => by
    have e : Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc * n + f (n - 1 - k)) (m + 1) =
        Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc * n + f (n - 1 - k)) m * n +
          f (n - 1 - m) := rfl
    rw [e, horner n f m (by omega), List.range_succ_eq_map, List.map_cons,
      List.map_map, Nat.ofDigits_cons]
    have e1 : n - 1 - m = n - (m + 1) + 0 := by omega
    have e2 : ((fun j => f (n - (m + 1) + j)) ∘ Nat.succ) = fun j => f (n - m + j) := by
      funext j
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [e1, e2]
    ring

theorem encW_eq (n w x : ℕ) : encW n w x = Nat.ofDigits n ((List.range n).map (imgW w x)) := by
  have e : encW n w x =
      Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc * n + imgW w x (n - 1 - k)) n := rfl
  rw [e, horner n _ n le_rfl]
  simp

theorem bit_eq (m i : ℕ) : Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1 = m.testBit i := by
  have e : Nat.land (Nat.shiftRight m i) 1 = m / 2 ^ i % 2 := by
    change (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem fixMaskW_eq (n w : ℕ) (L : List ℕ) :
    fixMaskW n w L = orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1
      (CFSG.KC.LQT.P.allL L fun a => Nat.beq (imgW w a i) i)) (fun i => i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : fixMaskW (n + 1) w L = Bool.rec (motive := fun _ => ℕ) (fixMaskW n w L)
        (Nat.lor (fixMaskW n w L) (Nat.shiftLeft 1 n))
        (CFSG.KC.LQT.P.allL L fun a => Nat.beq (imgW w a n) n) := rfl
    have e2 : orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1
        (CFSG.KC.LQT.P.allL L fun a => Nat.beq (imgW w a i) i)) (fun i => i) (n + 1) =
        Nat.lor (orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1
          (CFSG.KC.LQT.P.allL L fun a => Nat.beq (imgW w a i) i)) (fun i => i) n)
          (Nat.shiftLeft (Bool.rec (motive := fun _ => ℕ) 0 1
            (CFSG.KC.LQT.P.allL L fun a => Nat.beq (imgW w a n) n)) (Nat.mul 1 n)) := rfl
    rw [e1, e2, ← ih]
    cases CFSG.KC.LQT.P.allL L fun a => Nat.beq (imgW w a n) n
    · change fixMaskW n w L = fixMaskW n w L ||| (0 <<< (1 * n))
      rw [Nat.zero_shiftLeft, Nat.or_zero]
    · change fixMaskW n w L ||| (1 <<< n) = fixMaskW n w L ||| (1 <<< (1 * n))
      rw [Nat.one_mul]

theorem imgMaskW_eq (n w g m : ℕ) :
    imgMaskW n w g m = orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1 (m.testBit i))
      (imgW w g) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e1 : imgMaskW (n + 1) w g m = Bool.rec (motive := fun _ => ℕ) (imgMaskW n w g m)
        (Nat.lor (imgMaskW n w g m) (Nat.shiftLeft 1 (imgW w g n)))
        (Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1) := rfl
    have e2 : orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1 (m.testBit i)) (imgW w g)
        (n + 1) = Nat.lor (orW 1 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1 (m.testBit i))
          (imgW w g) n) (Nat.shiftLeft (Bool.rec (motive := fun _ => ℕ) 0 1 (m.testBit n))
          (Nat.mul 1 (imgW w g n))) := rfl
    rw [e1, e2, ← ih, bit_eq]
    cases m.testBit n
    · change imgMaskW n w g m = imgMaskW n w g m ||| (0 <<< (1 * imgW w g n))
      rw [Nat.zero_shiftLeft, Nat.or_zero]
    · change imgMaskW n w g m ||| (1 <<< imgW w g n) =
        imgMaskW n w g m ||| (1 <<< (1 * imgW w g n))
      rw [Nat.one_mul]

theorem boolRec_lt (b : Bool) : Bool.rec (motive := fun _ => ℕ) 0 1 b < 2 ^ 1 := by
  cases b <;> decide

@[expose] def indF {n : ℕ} (S : Finset (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ S then 1 else 0) else 0

theorem indF_lt {n : ℕ} (S : Finset (Fin n)) (i : ℕ) : indF S i < 2 ^ 1 := by
  unfold indF
  split_ifs <;> norm_num

theorem sum_two_pow_eq {n : ℕ} (S : Finset (Fin n)) :
    ∑ i ∈ S, 2 ^ (i : ℕ) = sumW 1 (indF S) n := by
  rw [sumW, ← Fin.sum_univ_eq_sum_range (fun i => indF S i * 2 ^ (1 * i)),
    ← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [indF, hi])]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp [indF, i.isLt, hi]

theorem imgW_sum_two_pow {n : ℕ} (S : Finset (Fin n)) (k : ℕ) :
    imgW 1 (∑ i ∈ S, 2 ^ (i : ℕ)) k = indF S k := by
  rw [sum_two_pow_eq, imgW_sumW (fun i _ => indF_lt S i)]
  split_ifs with hk
  · rfl
  · simp [indF, hk]

theorem testBit_sum_two_pow {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (∑ j ∈ S, 2 ^ (j : ℕ)).testBit i = decide (i ∈ S) := by
  have h := testBit_imgW 1 (∑ j ∈ S, 2 ^ (j : ℕ)) i 0
  rw [imgW_sum_two_pow, Nat.one_mul, Nat.add_zero] at h
  have h2 : (∑ j ∈ S, 2 ^ (j : ℕ)).testBit i = (indF S i).testBit 0 := by
    rw [h]
    simp
  rw [h2]
  simp only [indF, i.isLt, dite_true, Fin.eta]
  split_ifs with hi <;> simp [hi]

theorem sum_two_pow_lt {n : ℕ} (S : Finset (Fin n)) : ∑ i ∈ S, 2 ^ (i : ℕ) < 2 ^ n := by
  rw [sum_two_pow_eq]
  simpa using sumW_lt (w := 1) (m := n) fun i _ => indF_lt S i

theorem sum_two_pow_inj {n : ℕ} {S T : Finset (Fin n)}
    (h : ∑ i ∈ S, 2 ^ (i : ℕ) = ∑ i ∈ T, 2 ^ (i : ℕ)) : S = T := by
  ext i
  have := congrArg (fun m => m.testBit i) h
  simp only [testBit_sum_two_pow, decide_eq_decide] at this
  exact this

theorem sum_two_pow_pos {n : ℕ} {S : Finset (Fin n)} (h : S.Nonempty) :
    0 < ∑ i ∈ S, 2 ^ (i : ℕ) := by
  obtain ⟨i, hi⟩ := h
  apply Nat.pos_of_ne_zero
  intro h0
  have := testBit_sum_two_pow S i
  rw [h0, Nat.zero_testBit] at this
  simp [hi] at this

end CFSG.KC.LQT.PW

end
