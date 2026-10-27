module

public import CFSG.Certificates.Kernel.SporSch.J3F80.Pad
public import CFSG.Sporadic.Schreier.PairF2Sep

public section

namespace CFSG.KS.SporSch.J3F.Tri

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J3F CFSG.KS.SporSch.J3F.Pad
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Schreier.PairF2

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

private theorem nIf_eq (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem one_bit (k : Nat) : (1 : Nat).testBit k = decide (k = 0) := by
  cases k with
  | zero => simp
  | succ j => simp [Nat.testBit_succ]

private theorem lt_bit {x n k : Nat} (h : x < 2 ^ n) (hk : x.testBit k = true) : k < n := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))] at hk
  exact Bool.false_ne_true hk

private theorem pow_sub_bit {d a t : Nat} (ha : a ≤ d) :
    (2 ^ d - 2 ^ a).testBit t = (decide (a ≤ t) && decide (t < d)) := by
  have e : 2 ^ d - 2 ^ a = (2 ^ (d - a) - 1) <<< a := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← Nat.pow_add, Nat.sub_add_cancel ha]
  rw [e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  omega

private theorem wf_row_lt {X : Array Nat} (hX : Wf80 X) (i : Nat) : X[i]?.getD 0 < 2 ^ 80 := by
  by_cases hi : i < 80
  · exact hX.2 i hi
  · rw [Array.getElem?_eq_none (by have := hX.1; omega)]
    exact Nat.two_pow_pos _

private theorem wf_of_rows {X : Array Nat} (hs : X.size = 80)
    (h : ∀ i < 80, X[i]?.getD 0 < 2 ^ 80) : Wf80 X := ⟨hs, h⟩

private noncomputable def foldS (g : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => CFSG.KC.Enum.strictN acc fun a => Nat.lor a (g i)) n

private theorem foldS_bit (g : Nat → Nat) (n p : Nat) :
    (foldS g n).testBit p = true ↔ ∃ i < n, (g i).testBit p = true := by
  induction n with
  | zero => simp [foldS]
  | succ n ih =>
    have e : foldS g (n + 1) = foldS g n ||| g n := by
      change CFSG.KC.Enum.strictN (foldS g n) (fun a => Nat.lor a (g n)) = _
      rw [strictN_eq]
      rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i, hin, h⟩
      · have : i = n := by omega
        subst this
        exact Or.inr h

private theorem foldS_fields {g f : Nat → Nat} {n : Nat} (hg : ∀ i < n, g i = f i <<< (128 * i))
    (hf : ∀ i < n, f i < 2 ^ 128) (p : Nat) :
    (foldS g n).testBit p = (decide (p / 128 < n) && (f (p / 128)).testBit (p % 128)) := by
  apply Bool.eq_iff_iff.2
  rw [foldS_bit]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [hg i hi, Nat.testBit_shiftLeft] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at h
    obtain ⟨h1, h2⟩ := h
    have h3 := lt_bit (hf i hi) h2
    have e : p / 128 = i := by omega
    have e2 : p % 128 = p - 128 * i := by omega
    rw [e, e2]
    exact ⟨hi, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨p / 128, h1, ?_⟩
    rw [hg _ h1, Nat.testBit_shiftLeft]
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
    have e : p - 128 * (p / 128) = p % 128 := by omega
    rw [e]
    exact ⟨by omega, h2⟩

private theorem foldl_bit (g : Nat → Nat) (n p : Nat) :
    ((List.range n).foldl (fun acc i => acc ||| g i) 0).testBit p = true ↔
      ∃ i < n, (g i).testBit p = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or,
      Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hin : i < n
      · exact Or.inl ⟨i, hin, h⟩
      · have : i = n := by omega
        subst this
        exact Or.inr h

private theorem pidxK_eq (i : Nat) : pidxK i = pairIdx 80 i i := by
  unfold pidxK pairIdx
  rw [Nat.sub_self, Nat.add_zero]
  rfl

private def triR (z i : Nat) : Nat := ((z >>> pairIdx 80 i i) &&& (2 ^ (80 - i) - 1)) <<< i

private theorem tri_get (z : Nat) {i : Nat} (hi : i < 80) :
    (triRowsZ 80 z)[i]?.getD 0 = triR z i := by
  simp [triRowsZ, triR, hi]

private theorem triR_lt (z i : Nat) (hi : i < 80) : triR z i < 2 ^ 80 := by
  unfold triR
  rw [Nat.shiftLeft_eq]
  have h1 : (z >>> pairIdx 80 i i) &&& (2 ^ (80 - i) - 1) < 2 ^ (80 - i) :=
    Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := 80 - i); omega)
  calc _ < 2 ^ (80 - i) * 2 ^ i := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos i)
    _ = 2 ^ 80 := by rw [← Nat.pow_add]; congr 1; omega

private theorem triR_bit (z k s : Nat) :
    (triR z k).testBit (k + s) = (decide (s < 80 - k) && z.testBit (pairIdx 80 k k + s)) := by
  unfold triR
  rw [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  simp only [ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and,
    show k + s - k = s by omega]
  exact Bool.and_comm _ _

private theorem off_succ {k : Nat} (hk : k ≤ 80) :
    pairIdx 80 (k + 1) (k + 1) = pairIdx 80 k k + (80 - k) := by
  unfold pairIdx
  rw [Nat.sub_self, Nat.sub_self, Nat.add_zero, Nat.add_zero]
  cases k with
  | zero => simp
  | succ j =>
    have h1 : (j + 1 + 1) * (j + 1 + 1 - 1) / 2 = (j + 1) * (j + 1 - 1) / 2 + (j + 1) := by
      have : (j + 1 + 1) * (j + 1 + 1 - 1) = (j + 1) * (j + 1 - 1) + 2 * (j + 1) := by
        simp only [Nat.add_sub_cancel]; ring
      rw [this, Nat.add_mul_div_left _ _ (by norm_num)]
    have h2 : (j + 1) * (j + 1 - 1) / 2 ≤ 80 * (j + 1) := by
      calc (j + 1) * (j + 1 - 1) / 2 ≤ (j + 1) * (j + 1 - 1) := Nat.div_le_self _ _
        _ ≤ (j + 1) * 80 := Nat.mul_le_mul_left _ (by omega)
        _ = 80 * (j + 1) := Nat.mul_comm _ _
    rw [h1]
    generalize (j + 1) * (j + 1 - 1) / 2 = A at h2 ⊢
    omega

private theorem off_le {i : Nat} : ∀ k, i + 1 ≤ k → k ≤ 80 →
    pairIdx 80 i i + (80 - i) ≤ pairIdx 80 k k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro h; rw [off_succ (by omega)]
  | succ k hk ih =>
    intro h
    have := ih (by omega)
    rw [off_succ (by omega)]
    omega

private theorem off_cover : ∀ n, n ≤ 80 → ∀ m, m < pairIdx 80 n n →
    ∃ i < n, pairIdx 80 i i ≤ m ∧ m < pairIdx 80 i i + (80 - i) := by
  intro n
  induction n with
  | zero => intro _ m hm; simp [pairIdx] at hm
  | succ n ih =>
    intro hn m hm
    rw [off_succ (by omega)] at hm
    by_cases h : m < pairIdx 80 n n
    · obtain ⟨i, hi, h1, h2⟩ := ih (by omega) m h
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨n, by omega, by omega, hm⟩

private theorem off_80 : pairIdx 80 80 80 = 3240 := by decide

private theorem term_bit (U : Array Nat) (k m : Nat) :
    (((U[k]?.getD 0) >>> k) <<< pairIdx 80 k k).testBit m =
      (decide (pairIdx 80 k k ≤ m) && (U[k]?.getD 0).testBit (k + (m - pairIdx 80 k k))) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

private theorem pack_bit {U : Array Nat} (hU : Wf80 U) (m : Nat) :
    (packRowsZ 80 U).testBit m = true ↔
      ∃ k < 80, pairIdx 80 k k ≤ m ∧ (U[k]?.getD 0).testBit (k + (m - pairIdx 80 k k)) = true := by
  unfold packRowsZ
  rw [foldl_bit]
  simp only [term_bit, Bool.and_eq_true, decide_eq_true_eq]

private theorem pack_bit_row {U : Array Nat} (hU : Wf80 U) {i : Nat} (hi : i < 80) {s : Nat}
    (hs : s < 80 - i) :
    (packRowsZ 80 U).testBit (pairIdx 80 i i + s) = (U[i]?.getD 0).testBit (i + s) := by
  apply Bool.eq_iff_iff.2
  rw [pack_bit hU]
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    rcases Nat.lt_trichotomy k i with h | h | h
    · have := off_le (i := k) i (by omega) (by omega)
      have := lt_bit (wf_row_lt hU k) h2
      omega
    · subst h
      have : pairIdx 80 k k + s - pairIdx 80 k k = s := by omega
      rwa [this] at h2
    · have := off_le (i := i) k (by omega) (by omega)
      omega
  · intro h
    exact ⟨i, hi, by omega, by
      have : pairIdx 80 i i + s - pairIdx 80 i i = s := by omega
      rwa [this]⟩

private theorem usK_bit (p : Nat) :
    usK.testBit p =
      (decide (p / 128 < 80) && decide (p / 128 + 1 ≤ p % 128) && decide (p % 128 < 80)) := by
  have e : usK = foldS (fun i => Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 80)
      (Nat.shiftLeft 1 (Nat.succ i))) (Nat.mul 128 i)) 80 := rfl
  rw [e, foldS_fields (f := fun i => 2 ^ 80 - 2 ^ (i + 1))]
  · by_cases h : p / 128 < 80
    · rw [pow_sub_bit (by omega)]
      simp [h]
    · simp [h]
  · intro i _
    show (1 <<< 80 - 1 <<< (i + 1)) <<< (128 * i) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  · intro i _
    exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by norm_num) (by norm_num))

private theorem dgK_bit (p : Nat) :
    dgK.testBit p = (decide (p / 128 < 80) && decide (p / 128 = p % 128)) := by
  have e : dgK = foldS (fun i => Nat.shiftLeft 1 (Nat.mul 129 i)) 80 := rfl
  rw [e, foldS_fields (f := fun i => 2 ^ i)]
  · rw [Nat.testBit_two_pow]
  · intro i _
    show 1 <<< (129 * i) = _
    rw [Nat.one_shiftLeft, Nat.shiftLeft_eq, ← Nat.pow_add]
    congr 1
    omega
  · intro i hi
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem wf_tri (z : Nat) : Wf80 (triRowsZ 80 z) := by
  refine wf_of_rows (by simp [triRowsZ]) fun i hi => ?_
  rw [tri_get z hi]
  exact triR_lt z i hi

theorem triK_eq (z : Nat) : triK z = enc80 (triRowsZ 80 z) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [enc80_bit (wf_tri z) p]
  have e : triK z = foldS (fun i => Nat.shiftLeft (Nat.shiftLeft
      (Nat.land (Nat.shiftRight z (pidxK i))
        (Nat.sub (Nat.shiftLeft 1 (Nat.sub 80 i)) 1)) i) (Nat.mul 128 i)) 80 := rfl
  rw [e, foldS_fields (f := fun i => triR z i)]
  · by_cases h : p / 128 < 80
    · rw [tri_get z h]
    · simp [h]
  · intro i _
    show ((z >>> pidxK i) &&& ((1 <<< (80 - i)) - 1)) <<< i <<< (128 * i) = _
    rw [pidxK_eq, Nat.one_shiftLeft]
    rfl
  · intro i hi
    exact lt_of_lt_of_le (triR_lt z i hi) (Nat.pow_le_pow_right (by norm_num) (by norm_num))

theorem packTriK_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : Wf80 X) :
    packTriK rm (enc80 X) = packRowsZ 80 X := by
  apply Nat.eq_of_testBit_eq
  intro m
  apply Bool.eq_iff_iff.2
  have e : packTriK rm (enc80 X) = foldS (fun i => Nat.shiftLeft (Nat.shiftRight
      (rowJ rm (enc80 X) i) i) (pidxK i)) 80 := rfl
  rw [e, foldS_bit, pack_bit hX]
  refine exists_congr fun k => and_congr_right fun hk => ?_
  rw [rowJ80 hK hX hk, pidxK_eq]
  show ((X[k]?.getD 0 >>> k) <<< pairIdx 80 k k).testBit m = true ↔ _
  rw [term_bit]
  simp

private theorem canon_bit (X : Array Nat) {i : Nat} (t : Nat) (hi : i < 80) :
    ((canonRows 80 X)[i]?.getD 0).testBit t =
      ((decide (i + 1 ≤ t) &&
          xor ((X[i]?.getD 0).testBit t) (((transposeRows 80 X)[i]?.getD 0).testBit t)) ||
        ((X[i]?.getD 0).testBit t && decide (t = i))) := by
  simp only [canonRows, Array.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_xor, Nat.testBit_shiftLeft, one_bit]
  have e : ∀ b : Bool, (decide (t ≥ i + 1) && b) = (decide (i + 1 ≤ t) && b) := fun b => rfl
  by_cases h1 : i + 1 ≤ t
  · have e1 : i + 1 + (t - (i + 1)) = t := by omega
    simp [h1, e1, show ¬ t = i by omega, show ¬ t ≤ i by omega, show t - i ≠ 0 by omega]
  · by_cases h2 : t = i
    · subst h2; simp
    · simp [h1, h2, show ¬ t ≥ i by omega]

theorem canon_upper (C : Array Nat) {i j : Nat} (hi : i < 80) (hj : j < i) :
    ((canonRows 80 C)[i]?.getD 0).testBit j = false := by
  rw [canon_bit C j hi]
  simp [show ¬ i + 1 ≤ j by omega, show ¬ j = i by omega]

theorem canonK_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : Wf80 X) :
    Wf80 (canonRows 80 X) ∧
      canonK t0 t1 t2 t3 t4 t5 t6 usK dgK (enc80 X) = enc80 (canonRows 80 X) := by
  obtain ⟨hT, hTr⟩ := tr80 hK hX
  have hbit : ∀ (Y : Array Nat), Wf80 Y → ∀ i k, 80 ≤ k → (Y[i]?.getD 0).testBit k = false :=
    fun Y hY i k hk => Nat.testBit_lt_two_pow (lt_of_lt_of_le (wf_row_lt hY i)
      (Nat.pow_le_pow_right (by norm_num) hk))
  have hC : Wf80 (canonRows 80 X) := by
    refine wf_of_rows (by simp [canonRows]) fun i hi => ?_
    apply Nat.lt_pow_two_of_testBit
    intro k hk
    rw [canon_bit X k hi, hbit X hX i k hk, hbit _ hT i k hk]
    simp
  refine ⟨hC, ?_⟩
  unfold canonK
  rw [strictN_eq, hTr]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [enc80_bit hC p]
  change (((enc80 X ^^^ enc80 (transposeRows 80 X)) &&& usK) ||| (enc80 X &&& dgK)).testBit p = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor, enc80_bit hX,
    enc80_bit hT, usK_bit p, dgK_bit p]
  by_cases hq : p / 128 < 80
  · rw [canon_bit X _ hq]
    simp only [hq, decide_true, Bool.true_and]
    by_cases ht : p % 128 < 80
    · generalize (X[p / 128]?.getD 0).testBit (p % 128) = a
      generalize ((transposeRows 80 X)[p / 128]?.getD 0).testBit (p % 128) = b
      by_cases h1 : p / 128 + 1 ≤ p % 128 <;> by_cases h2 : p % 128 = p / 128 <;>
        cases a <;> cases b <;> simp [h1, h2, ht] <;> omega
    · rw [hbit X hX _ _ (by omega), hbit _ hT _ _ (by omega)]
      simp [ht]
  · simp [hq]

private theorem xor_enc80 {X Y : Array Nat} (hX : Wf80 X) (hY : Wf80 Y) :
    Wf80 (addRows X Y) ∧ enc80 X ^^^ enc80 Y = enc80 (addRows X Y) := by
  have hrow : ∀ i < 80, (addRows X Y)[i]?.getD 0 = (X[i]?.getD 0) ^^^ (Y[i]?.getD 0) := by
    intro i hi
    have hi1 : i < X.size := by rw [hX.1]; exact hi
    have hi2 : i < Y.size := by rw [hY.1]; exact hi
    have hi3 : i < (addRows X Y).size := by simp [addRows, hX.1, hY.1, hi]
    rw [Array.getElem?_eq_getElem hi3, Array.getElem?_eq_getElem hi1,
      Array.getElem?_eq_getElem hi2]
    simp [addRows]
  have hW : Wf80 (addRows X Y) := by
    refine wf_of_rows (by simp [addRows, hX.1, hY.1]) fun i hi => ?_
    rw [hrow i hi]
    exact Nat.xor_lt_two_pow (wf_row_lt hX i) (wf_row_lt hY i)
  refine ⟨hW, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_xor, enc80_bit hX, enc80_bit hY, enc80_bit hW]
  by_cases hq : p / 128 < 80
  · rw [hrow _ hq, Nat.testBit_xor]
    simp [hq]
  · simp [hq]

theorem polarK_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (z : Nat) :
    Wf80 (polarRowsZ 80 z) ∧ polarK t0 t1 t2 t3 t4 t5 t6 z = enc80 (polarRowsZ 80 z) := by
  obtain ⟨hT, hTr⟩ := tr80 hK (wf_tri z)
  obtain ⟨hW, hE⟩ := xor_enc80 (wf_tri z) hT
  refine ⟨hW, ?_⟩
  unfold polarK
  rw [strictN_eq, triK_eq, hTr]
  exact hE

private noncomputable def projR (D v k n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) D
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.xor acc (Nat.shiftLeft (Nat.shiftLeft 1 k) (Nat.mul 128 i)))
      (Nat.beq (Nat.land (Nat.shiftRight v i) 1) 1)) n

private theorem projR_bit {D v k : Nat} (hk : k < 80) (n p : Nat) :
    (projR D v k n).testBit p =
      (D.testBit p ^^ (decide (p / 128 < n) && v.testBit (p / 128) && decide (p % 128 = k))) := by
  induction n with
  | zero => simp [projR]
  | succ n ih =>
    have e : projR D v k (n + 1) = if v.testBit n = true then
        projR D v k n ^^^ ((1 <<< k) <<< (128 * n)) else projR D v k n := by
      change Bool.rec (motive := fun _ => Nat) (projR D v k n)
        (Nat.xor (projR D v k n) (Nat.shiftLeft (Nat.shiftLeft 1 k) (Nat.mul 128 n)))
        (Nat.beq (Nat.land (Nat.shiftRight v n) 1) 1) = _
      have h1 : Nat.land (Nat.shiftRight v n) 1 = if v.testBit n then 1 else 0 :=
        CFSG.KC.J4Q.and_one_bit v n
      rw [h1]
      cases hb : v.testBit n <;> simp [hb] <;> rfl
    rw [e]
    have hb : (1 <<< k <<< (128 * n)).testBit p = (decide (p / 128 = n) && decide (p % 128 = k)) := by
      rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, one_bit]
      apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
      omega
    by_cases hv : v.testBit n = true
    · rw [if_pos hv, Nat.testBit_xor, ih, hb]
      by_cases h1 : p / 128 = n
      · subst h1
        simp [hv]
      · simp [h1, show (p / 128 < n + 1) ↔ p / 128 < n by omega]
    · rw [if_neg hv, ih]
      by_cases h1 : p / 128 = n
      · subst h1
        simp [hv]
      · simp [h1, show (p / 128 < n + 1) ↔ p / 128 < n by omega]

theorem projK_eq {v k : Nat} (hk : k < 80) :
    Wf80 (projRows 80 v k) ∧ projK dgK v k = enc80 (projRows 80 v k) := by
  have hget : ∀ i < 80, (projRows 80 v k)[i]?.getD 0 =
      (1 <<< i) ^^^ (if v.testBit i then 1 <<< k else 0) := by
    intro i hi
    simp [projRows, hi]
  have hW : Wf80 (projRows 80 v k) := by
    refine wf_of_rows (by simp [projRows]) fun i hi => ?_
    rw [hget i hi]
    refine Nat.xor_lt_two_pow ?_ ?_
    · rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hi
    · split
      · rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hk
      · exact Nat.two_pow_pos _
  refine ⟨hW, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro p
  rw [enc80_bit hW p]
  change (projR dgK v k 80).testBit p = _
  rw [projR_bit hk, dgK_bit]
  by_cases hq : p / 128 < 80
  · rw [hget _ hq, Nat.testBit_xor]
    by_cases hv : v.testBit (p / 128) = true
    · simp only [hv, if_true]
      rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.testBit_two_pow]
      simp [hq, eq_comm]
    · simp only [hv, if_false]
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp [hq, hv, eq_comm]
  · simp [hq]

theorem colK_eq (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat} (hX : Wf80 X)
    (v : Nat) : colK rm t0 t1 t2 t3 t4 t5 t6 (enc80 X) v = mulVecRows 80 X v := by
  obtain ⟨hT, hTr⟩ := tr80 hK hX
  unfold colK
  rw [hTr, vec80 hK hT]
  rfl

theorem tri_pack {U : Array Nat} (hU : Wf80 U)
    (hup : ∀ i < 80, ∀ j < i, (U[i]?.getD 0).testBit j = false) :
    triRowsZ 80 (packRowsZ 80 U) = U := by
  have key : ∀ i < 80, triR (packRowsZ 80 U) i = U[i]?.getD 0 := by
    intro i hi
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases h1 : t < i
    · rw [hup i hi t h1]
      unfold triR
      rw [Nat.testBit_shiftLeft]
      simp [show ¬ t ≥ i by omega]
    · by_cases h2 : t < 80
      · obtain ⟨s, rfl⟩ : ∃ s, t = i + s := ⟨t - i, by omega⟩
        rw [triR_bit, pack_bit_row hU hi (by omega)]
        simp [show s < 80 - i by omega]
      · have e1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (wf_row_lt hU i)
          (Nat.pow_le_pow_right (by norm_num) (by omega : 80 ≤ t)))
        have e2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le (triR_lt (packRowsZ 80 U) i hi)
          (Nat.pow_le_pow_right (by norm_num) (by omega : 80 ≤ t)))
        rw [e1, e2]
  apply Array.ext
  · simp [triRowsZ, hU.1]
  · intro i h1 h2
    have hi : i < 80 := by simpa [triRowsZ] using h1
    have := key i hi
    rw [← tri_get _ hi] at this
    simpa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] using this

theorem pack_tri {z : Nat} (hz : z < 2 ^ 3240) : packRowsZ 80 (triRowsZ 80 z) = z := by
  apply Nat.eq_of_testBit_eq
  intro m
  apply Bool.eq_iff_iff.2
  rw [pack_bit (wf_tri z)]
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    rw [tri_get z hk, triR_bit] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    have e : pairIdx 80 k k + (m - pairIdx 80 k k) = m := by omega
    rw [e] at h2
    exact h2.2
  · intro h
    have hm : m < pairIdx 80 80 80 := by rw [off_80]; exact lt_bit hz h
    obtain ⟨i, hi, h1, h2⟩ := off_cover 80 le_rfl m hm
    refine ⟨i, hi, h1, ?_⟩
    rw [tri_get z hi, triR_bit]
    have e : pairIdx 80 i i + (m - pairIdx 80 i i) = m := by omega
    rw [e]
    simp [h, show m - pairIdx 80 i i < 80 - i by omega]

end CFSG.KS.SporSch.J3F.Tri

end

