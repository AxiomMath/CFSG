module

public import Certificates.Data.Kernel.SporSch.J3F80
public import CFSG.Certificates.Kernel.SporSch.J4SFormSound

public section

namespace CFSG.KS.SporSch.J3F.Pad

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J3F
open CFSG.Sporadic.SmallF2.Native

@[expose] def Wf80 (X : Array Nat) : Prop := X.size = 80 ∧ ∀ i < 80, X[i]?.getD 0 < 2 ^ 80

@[expose] def pad112 (X : Array Nat) : Array Nat := Array.ofFn (n := 112) fun i => X[i.val]?.getD 0

@[expose] def enc80 (X : Array Nat) : Nat := encN (pad112 X)

@[expose] def row80 (A r : Nat) : Nat := (A >>> (128 * r)) % 2 ^ 80

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem pdPadRow {X : Array Nat} (hs : X.size ≤ 112) (i : Nat) :
    (pad112 X)[i]?.getD 0 = X[i]?.getD 0 := by
  by_cases hi : i < 112
  · simp only [pad112, Array.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
  · rw [getElem?_neg _ i (by rw [pad112, Array.size_ofFn]; omega), getElem?_neg X i (by omega)]

private theorem pdBig {X : Array Nat} (hX : Wf80 X) {i : Nat} (hi : 80 ≤ i) : X[i]?.getD 0 = 0 := by
  rw [getElem?_neg X i (by rw [hX.1]; omega)]
  rfl

private theorem pdLt {X : Array Nat} (hX : Wf80 X) (i : Nat) : X[i]?.getD 0 < 2 ^ 80 := by
  by_cases hi : i < 80
  · exact hX.2 i hi
  · rw [pdBig hX (by omega)]
    exact Nat.two_pow_pos _

private theorem pdLtPow {X : Array Nat} (hX : Wf80 X) (i : Nat) {m : Nat} (hm : 80 ≤ m) :
    X[i]?.getD 0 < 2 ^ m :=
  Nat.lt_of_lt_of_le (pdLt hX i) (Nat.pow_le_pow_right (by omega) hm)

private theorem pdIteXor (b : Bool) (acc r : Nat) :
    (if b = true then acc ^^^ r else acc) = acc ^^^ (if b = true then r else 0) := by
  cases b <;> simp

private theorem pdFoldlXor (h : Nat → Nat) : ∀ (n acc : Nat),
    (List.range n).foldl (fun acc j => acc ^^^ h j) acc = acc ^^^ xsum h n
  | 0, acc => (Nat.xor_zero acc).symm
  | n + 1, acc => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pdFoldlXor h n acc,
      xsum_succ, Nat.xor_assoc]

private theorem pdVecEq (d : Nat) (R : Array Nat) (v : Nat) :
    vecMulN d R v = xsum (fun j => if v.testBit j then R[j]?.getD 0 else 0) d := by
  unfold vecMulN
  have e : (fun acc j => if v.testBit j = true then acc ^^^ R[j]?.getD 0 else acc) =
      (fun acc j => acc ^^^ (if v.testBit j = true then R[j]?.getD 0 else 0)) := by
    funext acc j
    exact pdIteXor _ _ _
  rw [e, pdFoldlXor, Nat.zero_xor]

private theorem pdXsumLt {f : Nat → Nat} {m : Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ m) →
    xsum f n < 2 ^ m
  | 0, _ => Nat.two_pow_pos m
  | n + 1, h => by
    rw [xsum_succ]
    exact Nat.xor_lt_two_pow (pdXsumLt fun k hk => h k (by omega)) (h n (by omega))

private theorem pdVecPad {Y : Array Nat} (hY : Wf80 Y) (w : Nat) :
    vecMulN 112 (pad112 Y) w = vecMulN 80 Y w := by
  rw [pdVecEq, pdVecEq, show (112 : Nat) = 80 + 32 from rfl, xsum_add]
  rw [xsum_zero (n := 32) (fun k _ => by
    rw [pdPadRow (by rw [hY.1]; omega), pdBig hY (by omega)]
    simp), Nat.xor_zero]
  exact xsum_congr fun k _ => by rw [pdPadRow (by rw [hY.1]; omega)]

private theorem pdVecMod (Y : Array Nat) (w : Nat) : vecMulN 80 Y (w % 2 ^ 80) = vecMulN 80 Y w := by
  rw [pdVecEq, pdVecEq]
  exact xsum_congr fun k hk => by rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]

private theorem pdVecZero (d : Nat) (Y : Array Nat) : vecMulN d Y 0 = 0 := by
  rw [pdVecEq]
  exact xsum_zero fun k _ => by simp

private theorem pdVecLt {Y : Array Nat} (hY : Wf80 Y) (v : Nat) : vecMulN 80 Y v < 2 ^ 80 := by
  rw [pdVecEq]
  exact pdXsumLt fun k _ => by
    split
    · exact pdLt hY k
    · exact Nat.two_pow_pos _

private theorem pdMulRow {X Y : Array Nat} (hX : WfN X) {i : Nat} (hi : i < 112) :
    (mulRows 112 X Y)[i]?.getD 0 = vecMulN 112 Y (X[i]?.getD 0) := by
  have hs : i < X.size := by rw [hX.1]; exact hi
  simp [mulRows, hs]

private theorem pdMul80Row {X Y : Array Nat} (hX : Wf80 X) (i : Nat) :
    (mulRows 80 X Y)[i]?.getD 0 = vecMulN 80 Y (X[i]?.getD 0) := by
  by_cases hi : i < 80
  · have hs : i < X.size := by rw [hX.1]; exact hi
    simp [mulRows, hs]
  · rw [pdBig hX (by omega), pdVecZero,
      getElem?_neg _ i (by unfold mulRows; rw [Array.size_map, hX.1]; omega)]
    rfl

private theorem pdEncCongr {X Y : Array Nat} (h : ∀ i < 112, X[i]?.getD 0 = Y[i]?.getD 0) :
    encN X = encN Y := by
  unfold encN
  have : ∀ l : List Nat, (∀ i ∈ l, i < 112) →
      l.foldr (fun i acc => Nat.lor (Nat.shiftLeft (X.getD i 0) (128 * i)) acc) 0 =
        l.foldr (fun i acc => Nat.lor (Nat.shiftLeft (Y.getD i 0) (128 * i)) acc) 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)),
        Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, h a (hl a List.mem_cons_self)]
  exact this _ fun i hi => List.mem_range.1 hi

private def pdRows (A : Nat) : Array Nat :=
  Array.ofFn (n := 112) fun r => (A >>> (128 * r.val)) % 2 ^ 112

private theorem pdRowsRow (A : Nat) {r : Nat} (hr : r < 112) :
    (pdRows A)[r]?.getD 0 = (A >>> (128 * r)) % 2 ^ 112 := by
  simp only [pdRows, Array.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some]

private theorem pdRowsWf (A : Nat) : WfN (pdRows A) :=
  wf_of_rows_tr (by rw [pdRows, Array.size_ofFn]) fun i hi => by
    rw [pdRowsRow A hi]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem pdRepBit (k : Nat) : ∀ m, (rep 1 128 m).testBit k =
    (List.range m).any (fun i => decide (k = 128 * i))
  | 0 => by simp [rep]
  | m + 1 => by
    have e : rep 1 128 (m + 1) = rep 1 128 m ||| (2 ^ (128 * m)) := by
      change rep 1 128 m ||| 1 <<< (128 * m) = _
      rw [Nat.one_shiftLeft]
    rw [e, Nat.testBit_or, pdRepBit k m, List.range_succ, List.any_append, Nat.testBit_two_pow]
    simp [eq_comm]

private theorem pdCBit (p : Nat) :
    (rep 1 128 112).testBit p = decide (p % 128 = 0 ∧ p / 128 < 112) := by
  rw [pdRepBit, Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨p / 128, h2, by omega⟩

private theorem pdCol (A : Nat) {k : Nat} (hk : k < 112) :
    Nat.land (Nat.shiftRight A k) (rep 1 128 112) =
      Nat.land (Nat.shiftRight (encN (pdRows A)) k) (rep 1 128 112) := by
  apply Nat.eq_of_testBit_eq
  intro p
  change (A >>> k &&& rep 1 128 112).testBit p = (encN (pdRows A) >>> k &&& rep 1 128 112).testBit p
  rw [Nat.testBit_and, Nat.testBit_and, pdCBit, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    encN_bit (pdRowsWf A)]
  by_cases h : p % 128 = 0 ∧ p / 128 < 112
  · have e1 : (k + p) / 128 = p / 128 := by omega
    have e2 : (k + p) % 128 = k := by omega
    rw [e1, e2, pdRowsRow A h.2, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    have e3 : 128 * (p / 128) + k = k + p := by omega
    rw [e3]
    simp [h, hk]
  · simp [h]

private theorem pdRecCongr (c rm A A' B : Nat)
    (h : ∀ k < 112, Nat.land (Nat.shiftRight A k) c = Nat.land (Nat.shiftRight A' k) c) :
    ∀ n, n ≤ 112 →
      Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => mstep c rm A B acc k) n =
        Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => mstep c rm A' B acc k) n
  | 0, _ => rfl
  | n + 1, hn => by
    change mstep c rm A B (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun k acc => mstep c rm A B acc k) n) n =
      mstep c rm A' B (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun k acc => mstep c rm A' B acc k) n) n
    rw [pdRecCongr c rm A A' B h n (by omega)]
    unfold mstep
    rw [h n (by omega)]

private theorem pdMulRead (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (A B : Nat) :
    mulJ c rm A B = mulJ c rm (encN (pdRows A)) B := by
  obtain ⟨hc, -⟩ := consts_c hK
  subst hc
  unfold mulJ
  rw [CFSG.KC.J4Q.strictN_eq, CFSG.KC.J4Q.strictN_eq, CFSG.KC.J4Q.strictN_eq,
    CFSG.KC.J4Q.strictN_eq]
  exact pdRecCongr _ _ _ _ _ (fun k hk => pdCol A hk) 112 (Nat.le_refl _)

private theorem pdTrRow {d : Nat} (X : Array Nat) {j : Nat} (hj : j < d) :
    (transposeRows d X)[j]?.getD 0 = ofBits d fun i => (X[i]?.getD 0).testBit j := by
  simp [transposeRows, hj]

private theorem pdStrictN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private noncomputable def pdDg (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun a => Nat.lor a (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 129) i)))
    m

private theorem pdDgBit : ∀ m p, (pdDg m).testBit p = decide (p % 129 = 0 ∧ p / 129 < m)
  | 0, p => by
    change (0 : Nat).testBit p = _
    simp
  | m + 1, p => by
    have e : pdDg (m + 1) = pdDg m ||| 2 ^ (129 * m) := by
      change strictN (pdDg m) (fun a => Nat.lor a (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 129) m))) = _
      rw [pdStrictN]
      change pdDg m ||| 1 <<< (129 * m) = _
      rw [Nat.one_shiftLeft]
    rw [e, Nat.testBit_or, pdDgBit m p, Nat.testBit_two_pow, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

private theorem pdIdRow {i : Nat} (hi : i < 80) : (idRows 80)[i]?.getD 0 = 2 ^ i := by
  simp [idRows, hi, Nat.one_shiftLeft]


theorem wf_pad {X : Array Nat} (hX : Wf80 X) : WfN (pad112 X) :=
  wf_of_rows_tr (by rw [pad112, Array.size_ofFn]) fun i _ => by
    rw [pdPadRow (by rw [hX.1]; omega)]
    exact pdLtPow hX i (by omega)

theorem enc80_bit {X : Array Nat} (hX : Wf80 X) (p : Nat) :
    (enc80 X).testBit p = (decide (p / 128 < 80) && (X[p / 128]?.getD 0).testBit (p % 128)) := by
  unfold enc80
  rw [encN_bit (wf_pad hX), pdPadRow (by rw [hX.1]; omega)]
  by_cases h : p / 128 < 80
  · simp [h, show p / 128 < 112 by omega]
  · rw [pdBig hX (by omega)]
    simp [h]

private theorem pdRow80 {X : Array Nat} (hX : Wf80 X) (r : Nat) :
    row80 (enc80 X) r = X[r]?.getD 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  unfold row80
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, enc80_bit hX]
  by_cases hj : j < 80
  · have e1 : (128 * r + j) / 128 = r := by omega
    have e2 : (128 * r + j) % 128 = j := by omega
    rw [e1, e2]
    by_cases hr : r < 80
    · simp [hj, hr]
    · rw [pdBig hX (by omega)]
      simp
  · rw [Nat.testBit_lt_two_pow (pdLtPow hX r (by omega))]
    simp [hj]

theorem enc80_inj {X Y : Array Nat} (hX : Wf80 X) (hY : Wf80 Y) (h : enc80 X = enc80 Y) : X = Y := by
  have hp := enc_inj (wf_pad hX) (wf_pad hY) h
  have hr : ∀ i, X[i]?.getD 0 = Y[i]?.getD 0 := fun i => by
    rw [← pdPadRow (X := X) (by rw [hX.1]; omega), ← pdPadRow (X := Y) (by rw [hY.1]; omega), hp]
  apply Array.ext
  · rw [hX.1, hY.1]
  · intro i h1 h2
    have := hr i
    rwa [getElem?_pos X i h1, getElem?_pos Y i h2, Option.getD_some, Option.getD_some] at this

private theorem pdBAnd {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem pdRowsAll : ∀ L : List Nat, List.rec (motive := fun _ => Bool) true
      (fun x _ ih => Bool.rec (motive := fun _ => Bool) false ih
        (Nat.blt x (Nat.shiftLeft (nat_lit 1) (nat_lit 80)))) L = true → ∀ x ∈ L, x < 2 ^ 80
  | [], _ => fun x hx => absurd hx List.not_mem_nil
  | y :: L, h => by
    obtain ⟨h1, h2⟩ := pdBAnd h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx'
    · have hlt : x < 1 <<< 80 := Eq.mp Nat.blt_eq h1
      rwa [Nat.one_shiftLeft] at hlt
    · exact pdRowsAll L h2 x hx'

private theorem pdPackBit : ∀ (L : List Nat), (∀ x ∈ L, x < 2 ^ 128) → ∀ p,
    (packRowsK L).testBit p = (L[p / 128]?.getD 0).testBit (p % 128)
  | [], _, p => by
    have e : packRowsK [] = 0 := rfl
    rw [e]
    simp
  | x :: L, hL, p => by
    have e : packRowsK (x :: L) = x ||| (packRowsK L <<< 128) := rfl
    rw [e, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hp : p < 128
    · rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
      simp [show ¬ 128 ≤ p by omega]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hL x List.mem_cons_self)
        (Nat.pow_le_pow_right (by omega) (by omega : 128 ≤ p))),
        pdPackBit L (fun y hy => hL y (List.mem_cons_of_mem _ hy)) (p - 128)]
      have e1 : p / 128 = (p - 128) / 128 + 1 := by omega
      have e2 : p % 128 = (p - 128) % 128 := by omega
      rw [e1, e2, List.getElem?_cons_succ]
      simp [show 128 ≤ p by omega]

theorem rows80K_sound {L : List Nat} (h : rows80K L = true) :
    Wf80 L.toArray ∧ packRowsK L = enc80 L.toArray := by
  unfold rows80K at h
  obtain ⟨h1, h2⟩ := pdBAnd h
  have hlen : L.length = 80 := Nat.eq_of_beq_eq_true h1
  have hlt := pdRowsAll L h2
  have hW : Wf80 L.toArray := ⟨by simp [hlen], fun i hi => by
    have hi' : i < L.length := by omega
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hi', Option.getD_some]
    exact hlt _ (List.getElem_mem hi')⟩
  refine ⟨hW, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro p
  rw [pdPackBit L (fun x hx => Nat.lt_of_lt_of_le (hlt x hx)
    (Nat.pow_le_pow_right (by omega) (by omega))), enc80_bit hW, List.getElem?_toArray]
  by_cases hp : p / 128 < 80
  · simp [hp]
  · rw [List.getElem?_eq_none (by omega)]
    simp

theorem mulJ_enc80 (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (A : Nat) {Y : Array Nat}
    (hY : Wf80 Y) :
    mulJ c rm A (enc80 Y) = encN (Array.ofFn (n := 112) fun r => vecMulN 80 Y (row80 A r.val)) := by
  rw [pdMulRead hK A (enc80 Y), enc80, ← (mulRows_enc hK (pdRowsWf A) (wf_pad hY)).2]
  apply pdEncCongr
  intro i hi
  rw [pdMulRow (pdRowsWf A) hi, pdRowsRow A hi, pdVecPad hY]
  simp only [Array.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
  unfold row80
  rw [← pdVecMod Y ((A >>> (128 * i)) % 2 ^ 112),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 80 ≤ 112))]

theorem mul80 (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y : Array Nat} (hX : Wf80 X)
    (hY : Wf80 Y) :
    Wf80 (mulRows 80 X Y) ∧ mulJ c rm (enc80 X) (enc80 Y) = enc80 (mulRows 80 X Y) := by
  have hW : Wf80 (mulRows 80 X Y) := ⟨by unfold mulRows; rw [Array.size_map, hX.1], fun i _ => by
    rw [pdMul80Row hX]
    exact pdVecLt hY _⟩
  refine ⟨hW, ?_⟩
  rw [mulJ_enc80 hK _ hY]
  show encN _ = encN (pad112 _)
  apply pdEncCongr
  intro i hi
  simp only [Array.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
  rw [pdRow80 hX, pdPadRow (by rw [hW.1]; omega), pdMul80Row hX]

theorem tr80 (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : Wf80 X) :
    Wf80 (transposeRows 80 X) ∧
      trJ t0 t1 t2 t3 t4 t5 t6 (enc80 X) = enc80 (transposeRows 80 X) := by
  have hW : Wf80 (transposeRows 80 X) := ⟨by simp [transposeRows], fun j hj => by
    rw [pdTrRow X hj]
    exact CFSG.Sporadic.SmallF2.ofBits_lt _ _⟩
  refine ⟨hW, ?_⟩
  unfold enc80
  rw [← (tr_enc_proved hK (wf_pad hX)).2]
  apply pdEncCongr
  intro j hj
  rw [pdTrRow _ hj, pdPadRow (by rw [hW.1]; omega)]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [CFSG.Sporadic.SmallF2.ofBits_testBit, pdPadRow (by rw [hX.1]; omega)]
  by_cases hj80 : j < 80
  · rw [pdTrRow X hj80, CFSG.Sporadic.SmallF2.ofBits_testBit]
    by_cases hq : q < 80
    · simp [hq, show q < 112 by omega]
    · rw [pdBig hX (by omega)]
      simp
  · rw [getElem?_neg _ j (by rw [hW.1]; omega), Option.getD_none,
      Nat.testBit_lt_two_pow (pdLtPow hX q (by omega))]
    simp

theorem id80 : Wf80 (idRows 80) ∧ dgK = enc80 (idRows 80) := by
  have hW : Wf80 (idRows 80) := ⟨by simp [idRows], fun i hi => by
    rw [pdIdRow hi]
    exact Nat.pow_lt_pow_right (by omega) hi⟩
  refine ⟨hW, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro p
  rw [enc80_bit hW, show dgK = pdDg 80 from rfl, pdDgBit]
  by_cases hp : p / 128 < 80
  · rw [pdIdRow hp, Nat.testBit_two_pow, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    omega
  · rw [pdBig hW (by omega), Nat.zero_testBit, Bool.and_false, decide_eq_false_iff_not]
    omega

theorem vec80 (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : Wf80 X)
    (v : Nat) : vecJ rm v (enc80 X) = vecMulN 80 X v := by
  rw [enc80, ← vec_enc hK (wf_pad hX), pdVecPad hX]

theorem rowJ80 (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : Wf80 X)
    {i : Nat} (hi : i < 80) : rowJ rm (enc80 X) i = X[i]?.getD 0 := by
  obtain ⟨-, hrm⟩ := consts_c hK
  subst hrm
  apply Nat.eq_of_testBit_eq
  intro j
  change ((enc80 X >>> (i * 128)) &&& (2 ^ 112 - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, enc80_bit hX]
  by_cases hj : j < 112
  · have e1 : (i * 128 + j) / 128 = i := by omega
    have e2 : (i * 128 + j) % 128 = j := by omega
    rw [e1, e2]
    by_cases hj80 : j < 80
    · simp [hj, hi]
    · rw [Nat.testBit_lt_two_pow (pdLtPow hX i (by omega))]
      simp
  · rw [Nat.testBit_lt_two_pow (pdLtPow hX i (by omega))]
    simp [hj]

end CFSG.KS.SporSch.J3F.Pad

end
