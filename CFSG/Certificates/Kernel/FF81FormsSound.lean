module

public import Certificates.Data.Kernel.FF81Forms
public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs

public section

namespace CFSG.KC.FF81F

open Matrix CFSG.RankThree.PartTwo.Sec21.FF81.GL6

@[expose] def decK (a : Nat) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => if a.testBit (6 * i.val + j.val) then 1 else 0

@[expose] def Fm (S W X : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Wᵀ * (Sᵀ * X * S) * W + Sᵀ * X * S

theorem bitK_eq (a t : Nat) : bitK a t = a.testBit t := by
  change Nat.beq ((a >>> t) &&& 1) 1 = a.testBit t
  unfold Nat.testBit
  generalize a >>> t = x
  rw [Nat.and_one_is_mod]
  try rw [Nat.one_and_eq_mod_two]
  try rw [Nat.and_one_is_mod]
  have hx : x % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize x % 2 = y at *
  interval_cases y <;> rfl

theorem xorB_eq (x y : Bool) : xorB x y = (x ^^ y) := by cases x <;> cases y <;> rfl

theorem packK_succ (f : Nat → Bool) (m : Nat) :
    packK f (m + 1) = packK f m + (if f m then 2 ^ m else 0) := by
  change packK f m + nIf(f m, Nat.pow 2 m, 0) = _
  cases f m <;> rfl

theorem packK_lt (f : Nat → Bool) (m : Nat) : packK f m < 2 ^ m := by
  induction m with
  | zero => exact Nat.zero_lt_one
  | succ m ih =>
    rw [packK_succ, Nat.pow_succ]
    split <;> omega

theorem testBit_packK (f : Nat → Bool) (m q : Nat) :
    (packK f m).testBit q = (decide (q < m) && f q) := by
  induction m with
  | zero =>
    change (0 : Nat).testBit q = _
    simp
  | succ m ih =>
    rw [packK_succ]
    have hlt := packK_lt f m
    by_cases hf : f m = true
    · rw [if_pos hf, Nat.add_comm]
      rcases Nat.lt_trichotomy q m with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]
        simp [h, Nat.lt_succ_of_lt h]
      · subst h
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        simp [hf]
      · have h2 : 2 ^ m + packK f m < 2 ^ q :=
          lt_of_lt_of_le (by rw [Nat.pow_succ] at *; omega)
            (Nat.pow_le_pow_right (by omega) (Nat.succ_le_of_lt h))
        rw [Nat.testBit_lt_two_pow h2]
        simp [show ¬ q < m + 1 by omega]
    · rw [if_neg hf, Nat.add_zero, ih]
      rcases Nat.lt_or_ge q m with h | h
      · simp [h, Nat.lt_succ_of_lt h]
      · rcases Nat.eq_or_lt_of_le h with h | h
        · subst h
          simp [hf]
        · simp [show ¬ q < m by omega, show ¬ q < m + 1 by omega]

theorem ite_xor (x y : Bool) :
    (if (x ^^ y) = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) + (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

theorem ite_and (x y : Bool) :
    (if (x && y) = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) * (if y = true then 1 else 0) := by
  cases x <;> cases y <;> decide

theorem entK_eq (a b i j : Nat) : entK a b i j =
    (((((((false ^^ (a.testBit (6 * i + 0) && b.testBit (6 * 0 + j))) ^^
      (a.testBit (6 * i + 1) && b.testBit (6 * 1 + j))) ^^
      (a.testBit (6 * i + 2) && b.testBit (6 * 2 + j))) ^^
      (a.testBit (6 * i + 3) && b.testBit (6 * 3 + j))) ^^
      (a.testBit (6 * i + 4) && b.testBit (6 * 4 + j))) ^^
      (a.testBit (6 * i + 5) && b.testBit (6 * 5 + j)))) := by
  simp only [← bitK_eq, ← xorB_eq]
  rfl

theorem decK_mulK (a b : Nat) : decK (mulK a b) = decK a * decK b := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have h1 : (6 * i.val + j.val) / 6 = i.val := by omega
  have h2 : (6 * i.val + j.val) % 6 = j.val := by omega
  have h3 : 6 * i.val + j.val < 36 := by omega
  simp only [decK, mulK, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_six, testBit_packK]
  change (if (decide (6 * i.val + j.val < 36) &&
    entK a b ((6 * i.val + j.val) / 6) ((6 * i.val + j.val) % 6)) = true then _ else _) = _
  rw [h1, h2, entK_eq]
  simp only [h3, decide_true, Bool.true_and, ite_xor, ite_and]
  simp

theorem decK_trK (a : Nat) : decK (trK a) = (decK a)ᵀ := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  have h1 : (6 * i.val + j.val) / 6 = i.val := by omega
  have h2 : (6 * i.val + j.val) % 6 = j.val := by omega
  have h3 : 6 * i.val + j.val < 36 := by omega
  simp only [decK, trK, Matrix.of_apply, Matrix.transpose_apply, testBit_packK]
  change (if (decide (6 * i.val + j.val < 36) && bitK a (Nat.add (Nat.mul 6
    ((6 * i.val + j.val) % 6)) ((6 * i.val + j.val) / 6))) = true then _ else _) = _
  rw [h1, h2, bitK_eq]
  simp [h3]

theorem decK_xor (a b : Nat) : decK (Nat.xor a b) = decK a + decK b := by
  ext i j
  change (if (a ^^^ b).testBit _ = true then _ else _) = _
  simp only [decK, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor, ite_xor]

theorem decK_zero : decK 0 = 0 := by
  ext i j
  simp [decK]

theorem decK_nIf (b : Bool) (c : Nat) :
    decK (nIf(b, c, 0)) = if b = true then decK c else 0 := by
  cases b
  · exact decK_zero
  · rfl

theorem decK_nIf_smul (b : Bool) (c : Nat) :
    decK (nIf(b, c, 0)) = (if b = true then (1 : ZMod 2) else 0) • decK c := by
  cases b
  · rw [decK_zero]
    simp
  · simp

theorem decK_fK (s w e : Nat) : decK (fK s w e) = Fm (decK s) (decK w) (decK e) := by
  simp only [fK, gK, decK_xor, decK_mulK, decK_trK, Fm]

theorem Fm_add (S W X Y : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Fm S W (X + Y) = Fm S W X + Fm S W Y := by
  simp only [Fm, Matrix.mul_add, Matrix.add_mul]
  abel

theorem Fm_zero (S W : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Fm S W 0 = 0 := by
  simp [Fm]

theorem Fm_ite (S W X : Matrix (Fin 6) (Fin 6) (ZMod 2)) (b : Bool) :
    Fm S W (if b = true then X else 0) = if b = true then Fm S W X else 0 := by
  cases b
  · simp [Fm_zero]
  · simp

theorem linK_nil (n : Nat) : linK [] n = 0 := rfl

theorem linK_cons (c : Nat) (cs : List Nat) (n : Nat) :
    linK (c :: cs) n = Nat.xor (nIf(bitK n 0, c, 0)) (linK cs (n >>> 1)) := rfl

theorem decK_linK_cols (s w : Nat) (cs es : List Nat) (n : Nat) (h : colsK s w cs es = true) :
    decK (linK cs n) = Fm (decK s) (decK w) (decK (linK es n)) := by
  induction cs generalizing es n with
  | nil =>
    cases es with
    | nil => simp only [linK_nil, decK_zero, Fm_zero]
    | cons e es => exact absurd h Bool.false_ne_true
  | cons c cs ih =>
    cases es with
    | nil => exact absurd h Bool.false_ne_true
    | cons e es =>
      change bAnd(Nat.beq c (fK s w e), colsK s w cs es) = true at h
      cases hc : Nat.beq c (fK s w e)
      · rw [hc] at h
        exact absurd h Bool.false_ne_true
      · rw [hc] at h
        have hce : c = fK s w e := Nat.eq_of_beq_eq_true hc
        rw [linK_cons, linK_cons, decK_xor, decK_xor, decK_nIf, decK_nIf, ih es _ h, Fm_add,
          Fm_ite, hce, decK_fK]

def nOf (bs : List Bool) : Nat := bs.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0

theorem nOf_lt (bs : List Bool) : nOf bs < 2 ^ bs.length := by
  induction bs with
  | nil => exact Nat.zero_lt_one
  | cons b bs ih =>
    change (if b then 1 else 0) + 2 * nOf bs < 2 ^ (bs.length + 1)
    rw [Nat.pow_succ]
    split <;> omega

theorem bitK_nOf (b : Bool) (bs : List Bool) : bitK (nOf (b :: bs)) 0 = b := by
  rw [bitK_eq, Nat.testBit_zero]
  change decide (((if b then 1 else 0) + 2 * nOf bs) % 2 = 1) = b
  cases b <;> simp <;> omega

theorem shift_nOf (b : Bool) (bs : List Bool) : nOf (b :: bs) >>> 1 = nOf bs := by
  rw [Nat.shiftRight_eq_div_pow]
  change ((if b then 1 else 0) + 2 * nOf bs) / 2 ^ 1 = nOf bs
  cases b <;> simp <;> omega

theorem nOf_lt15 (bs : List Bool) (h : bs.length = 15) : nOf bs < 32768 := by
  have := nOf_lt bs
  rw [h] at this
  exact this

theorem ite_decide_one (x : ZMod 2) : (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by
  fin_cases x <;> rfl

theorem ite_eq_one (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  fin_cases x <;> rfl

theorem exists_index (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hsym : ∀ i j, P j i = P i j)
    (hdiag : ∀ i, P i i = 0) : ∃ n, n < 32768 ∧ decK (linK ES n) = P := by
  let bs : List Bool := [decide (P 0 1 = 1), decide (P 0 2 = 1), decide (P 0 3 = 1),
    decide (P 0 4 = 1), decide (P 0 5 = 1), decide (P 1 2 = 1), decide (P 1 3 = 1),
    decide (P 1 4 = 1), decide (P 1 5 = 1), decide (P 2 3 = 1), decide (P 2 4 = 1),
    decide (P 2 5 = 1), decide (P 3 4 = 1), decide (P 3 5 = 1), decide (P 4 5 = 1)]
  refine ⟨nOf bs, nOf_lt15 bs rfl, ?_⟩
  simp only [bs, ES, linK_cons, linK_nil, bitK_nOf, shift_nOf, decK_xor, decK_nIf_smul,
    decK_zero, add_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := { decide := true }) [decK, ite_decide_one, ite_eq_one, Matrix.smul_apply,
      Matrix.add_apply, Matrix.zero_apply, hdiag, hsym 0 1, hsym 0 2,
      hsym 0 3, hsym 0 4, hsym 0 5, hsym 1 2, hsym 1 3, hsym 1 4, hsym 1 5, hsym 2 3, hsym 2 4,
      hsym 2 5, hsym 3 4, hsym 3 5, hsym 4 5]

theorem decK_J0K : decK J0K = J0 := by decide

theorem decK_U0K : decK U0K = u0M := by decide

theorem decK_ONEK : decK ONEK = 1 := by decide

theorem linK_ES_J0 : decK (linK ES 2180) = J0 := by decide

theorem decK_inj {a b : Nat} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : decK a = decK b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q 36 with hq | hq
  · have e := congrFun (congrFun h ⟨q / 6, by omega⟩) ⟨q % 6, by omega⟩
    simp only [decK, Matrix.of_apply, show 6 * (q / 6) + q % 6 = q by omega] at e
    cases ha' : a.testBit q <;> cases hb' : b.testBit q <;> simp_all
  · have h36 : 2 ^ 36 ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hq
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem mulK_lt (a b : Nat) : mulK a b < 2 ^ 36 := packK_lt _ 36

theorem bAnd_eq_true (a b : Bool) :
    (Bool.rec (motive := fun _ => Bool) false b a) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem bNot_eq_true (a : Bool) :
    (Bool.rec (motive := fun _ => Bool) true false a) = true ↔ a = false := by
  cases a <;> simp

theorem pair_sound (x : Nat × Nat × Nat × Nat × List Nat) (h : pairOK x = true) :
    ∃ s w : G6, (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) = decK x.1 ∧
      (w : Matrix (Fin 6) (Fin 6) (ZMod 2)) = decK x.2.2.1 ∧ s ∈ Sp0 ∧ w * u0 = u0 * w ∧
      w ∉ Sp0 ∧ colsK x.1 x.2.2.1 x.2.2.2.2 ES = true := by
  obtain ⟨s, si, w, wi, cs⟩ := x
  simp only [pairOK, bAnd_eq_true, bNot_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have e1 := congrArg decK (Nat.eq_of_beq_eq_true h1)
  have e2 := congrArg decK (Nat.eq_of_beq_eq_true h2)
  have e3 := congrArg decK (Nat.eq_of_beq_eq_true h3)
  have e4 := congrArg decK (Nat.eq_of_beq_eq_true h4)
  have e5 := congrArg decK (Nat.eq_of_beq_eq_true h5)
  have e6 := congrArg decK (Nat.eq_of_beq_eq_true h6)
  simp only [decK_mulK, decK_trK, decK_ONEK, decK_J0K, decK_U0K] at e1 e2 e3 e4 e5 e6
  refine ⟨⟨decK s, decK si, e1, e2⟩, ⟨decK w, decK wi, e4, e5⟩, rfl, rfl, e3, ?_, ?_, h8⟩
  · apply Units.ext
    exact e6
  · intro hw
    have hne := Nat.ne_of_beq_eq_false h7
    apply hne
    apply decK_inj (mulK_lt _ _) (by decide)
    rw [decK_mulK, decK_mulK, decK_trK, decK_J0K]
    exact hw

end CFSG.KC.FF81F

end
