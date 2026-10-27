module

public import Certificates.Data.Kernel.SporSch.F2Mat
public import Certificates.Data.CFSGNative.Co3Schreier.Forms
import CFSG.Certificates.Kernel.SporSch.F2PayRun
public import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch

open CFSG.KS.Raw CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Schreier.Co3.Native

theorem payRun_eq (d : Nat) (cs : List Char) :
    rowsOfPayload d (String.ofList cs) = unpack d d (payRun d cs 0 0 0) :=
  F2P.payRun_rowsHS d cs


section Proofs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Schreier.Co3.Native
open CFSG.KS.SporSch.M24.ActL (xs xs_cons xs_nil xs_congr xs_false testBit_vecMulN
  testBit_ofBits)
open CFSG.KS.Raw.Orb (foldN_eq)

theorem bitN_eq (x k : Nat) : bitN x k = if x.testBit k then 1 else 0 := by
  have e : bitN x k = x / 2 ^ k % 2 := by
    change (x >>> k) &&& 1 = _
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

theorem beq_bitN (x k : Nat) : Nat.beq (bitN x k) 1 = x.testBit k := by
  rw [bitN_eq]
  cases x.testBit k <;> rfl

theorem ble_dec (a b : Nat) : Nat.ble a b = decide (a ≤ b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.ble_eq, decide_eq_true_iff])

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem allLt_iff' {n : Nat} {p : Nat → Bool} :
    CFSG.Monster.B.Co2.Native.allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    simpa using h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h ⟨i, hi⟩ _
    simpa using h i hi

theorem xorFold_testBit (c : Nat → Bool) (r : Nat → Nat) (i : Nat) : ∀ l : List Nat,
    (l.foldr (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (r j)) (c j))
      0).testBit i = xs (fun j => c j && (r j).testBit i) l
  | [] => by simp [xs_nil]
  | a :: l => by
    have ih := xorFold_testBit c r i l
    have ex : ∀ x y : Nat, Nat.xor x y = x ^^^ y := fun _ _ => rfl
    rw [List.foldr_cons, xs_cons]
    cases c a
    · simpa using ih
    · change (Nat.xor _ (r a)).testBit i = _
      rw [ex, Nat.testBit_xor, ih]
      simp [Bool.xor_comm]

theorem orFold_testBit (c : Nat → Bool) (k : Nat) : ∀ l : List Nat,
    (l.foldr (fun j acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.lor acc (Nat.shiftLeft 1 j)) (c j)) 0).testBit k = (decide (k ∈ l) && c k)
  | [] => by simp
  | a :: l => by
    have ih := orFold_testBit c k l
    have eo : ∀ x y : Nat, Nat.lor x y = x ||| y := fun _ _ => rfl
    rw [List.foldr_cons]
    cases hc : c a
    · change (List.foldr _ 0 l).testBit k = _
      rw [ih]
      by_cases hk : k = a
      · subst hk
        simp [hc]
      · simp [hk]
    · change (Nat.lor _ (Nat.shiftLeft 1 a)).testBit k = _
      have es : Nat.shiftLeft 1 a = 2 ^ a := Nat.one_shiftLeft a
      rw [eo, Nat.testBit_or, ih, es, Nat.testBit_two_pow]
      by_cases hk : k = a
      · subst hk
        simp [hc]
      · simp [hk, Ne.symm hk]

theorem rowP_lt (d M i : Nat) : rowP d M i < 2 ^ d := CFSG.KS.PackFld.pg_lt d M i

theorem unpack_get (d X : Nat) {j : Nat} (hj : j < d) : (unpack d d X)[j]?.getD 0 = rowP d X j := by
  simp [unpack, hj]
  rfl

theorem unpack_get! (d X : Nat) {j : Nat} (hj : j < d) : (unpack d d X)[j]! = rowP d X j := by
  rw [getElem!_pos _ j (by simpa [unpack] using hj)]
  simp [unpack]
  rfl

theorem vmP_testBit (d M v i : Nat) :
    (vmP d M v).testBit i = xs (fun j => v.testBit j && (rowP d M j).testBit i) (List.range d) := by
  unfold vmP
  rw [foldN_eq, xorFold_testBit]
  refine xs_congr fun j _ => ?_
  rw [beq_bitN]

theorem vmP_eq (d Y v : Nat) : vmP d Y v = vecMulN d (unpack d d Y) v :=
  Nat.eq_of_testBit_eq fun i => by
    rw [vmP_testBit, testBit_vecMulN]
    refine xs_congr fun j hj => ?_
    rw [unpack_get _ _ (List.mem_range.1 hj)]

theorem vmP_lt (d M v : Nat) : vmP d M v < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [vmP_testBit, xs_congr (g := fun _ => false), xs_false]
  intro j _
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rowP_lt d M j) (Nat.pow_le_pow_right
    (by omega) hi)), Bool.and_false]

theorem fld_packR_list (d : Nat) (f : Nat → Nat) : ∀ l : List Nat, (∀ i ∈ l, f i < 2 ^ d) →
    CFSG.KS.PackFld.Fld d (l.foldr (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul d i)))
      0) (fun j => if j ∈ l then f j else 0)
  | [], _ => CFSG.KS.PackFld.fld_congr (CFSG.KS.PackFld.fld_zero d) fun j => by simp
  | a :: l, h => by
    have ih := fld_packR_list d f l fun i hi => h i (List.mem_cons_of_mem _ hi)
    have ha := h a List.mem_cons_self
    have h2 := CFSG.KS.PackFld.fld_shl a (CFSG.KS.PackFld.fld_one ha)
    have e : ∀ x y : Nat, Nat.lor x (Nat.shiftLeft y (Nat.mul d a)) = x ||| y <<< (d * a) :=
      fun _ _ => rfl
    rw [List.foldr_cons, e]
    refine CFSG.KS.PackFld.fld_congr (CFSG.KS.PackFld.fld_or ih h2) fun j => ?_
    by_cases hj : j = a
    · subst hj
      by_cases hm : j ∈ l
      · simp [hm]
      · simp [hm]
    · by_cases hja : a ≤ j
      · have : j - a ≠ 0 := by omega
        simp [hj, hja, this]
      · simp [hj, hja]

theorem fld_packR {d : Nat} {f : Nat → Nat} (h : ∀ i < d, f i < 2 ^ d) :
    CFSG.KS.PackFld.Fld d (packR d f) (fun j => if j < d then f j else 0) := by
  have e := fld_packR_list d f (List.range d) fun i hi => h i (List.mem_range.1 hi)
  unfold packR
  rw [foldN_eq]
  exact CFSG.KS.PackFld.fld_congr e fun j => by simp

theorem unpack_packR_proved {d : Nat} {f : Nat → Nat} (h : ∀ i < d, f i < 2 ^ d) :
    unpack d d (packR d f) = Array.ofFn (n := d) fun i => f i.val := by
  apply Array.ext
  · simp [unpack]
  · intro i h1 _
    have hi : i < d := by simpa [unpack] using h1
    simp only [unpack, Array.getElem_ofFn]
    have := CFSG.KS.PackFld.pg_of_fld (i := i) (fld_packR h) (by simpa [hi] using h i hi)
    simpa [hi] using this

theorem mulP_eq_proved (d X Y : Nat) :
    mulRows d (unpack d d X) (unpack d d Y) = unpack d d (mulP d X Y) := by
  unfold mulP
  rw [unpack_packR_proved fun i _ => vmP_lt d Y _]
  apply Array.ext
  · simp [mulRows, unpack]
  · intro i h1 _
    have hi : i < d := by simpa [mulRows, unpack] using h1
    simp only [mulRows, Array.getElem_map, Array.getElem_ofFn]
    rw [vmP_eq]
    simp [unpack]
    rfl

theorem idP_eq_proved (d : Nat) : idRows d = unpack d d (idP d) := by
  unfold idP
  rw [unpack_packR_proved fun i hi => by
    have es : Nat.shiftLeft 1 i = 2 ^ i := Nat.one_shiftLeft i
    rw [es]
    exact Nat.pow_lt_pow_right (by omega) hi]
  apply Array.ext
  · simp [idRows]
  · intro i h1 _
    simp only [idRows, Array.getElem_ofFn]
    rfl

theorem powP_eq_proved (d M e : Nat) : powRows d (unpack d d M) e = unpack d d (powP d M e) := by
  induction e with
  | zero => exact idP_eq_proved d
  | succ e ih =>
    have e1 : powP d M (e + 1) = mulP d (powP d M e) M := by
      change strictN (powP d M e) (fun a => mulP d a M) = mulP d (powP d M e) M
      exact Orb.strictN_eq _ _
    rw [powRows, ih, e1, mulP_eq_proved]

theorem orCol_lt (d : Nat) (c : Nat → Bool) :
    (List.range d).foldr (fun j acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.lor acc (Nat.shiftLeft 1 j)) (c j)) 0 < 2 ^ d := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [orFold_testBit]
  simp only [List.mem_range]
  simp [show ¬ i < d by omega]

theorem transP_eq (d M : Nat) : transposeRows d (unpack d d M) = unpack d d (transP d M) := by
  unfold transP
  rw [unpack_packR_proved fun j _ => by rw [foldN_eq]; exact orCol_lt d _]
  apply Array.ext
  · simp [transposeRows]
  · intro j h1 _
    simp only [transposeRows, Array.getElem_ofFn]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [testBit_ofBits, foldN_eq, orFold_testBit]
    simp only [List.mem_range]
    by_cases hk : k < d
    · simp only [hk, decide_true, Bool.true_and]
      rw [unpack_get _ _ hk, beq_bitN]
    · simp [hk]

theorem pidx_eq (i j : Nat) : pidx i j = pairIdx22 i j := rfl

theorem triP_eq (t : Nat) : triRows t = unpack 22 22 (triP t) := by
  unfold triP
  rw [unpack_packR_proved fun j _ => by rw [foldN_eq]; exact orCol_lt 22 _]
  apply Array.ext
  · simp [triRows]
  · intro i h1 _
    simp only [triRows, Array.getElem_ofFn]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [testBit_ofBits, foldN_eq, orFold_testBit]
    simp only [List.mem_range]
    by_cases hk : k < 22
    · simp only [hk, decide_true, Bool.true_and, Orb.bAnd_eq, ble_dec, beq_bitN, pidx_eq]
    · simp [hk]

theorem coefOK_of {C t : Nat} (h : coefOKK C t = true) : coefOK (unpack 22 22 C) t = true := by
  unfold coefOKK at h
  unfold coefOK
  rw [allLt_iff']
  intro i hi
  rw [allLt_iff']
  intro j hj
  have h1 := Orb.allN_iff.1 (Orb.allN_iff.1 h i hi) j hj
  rw [Orb.bIf_eq] at h1
  by_cases hij : i ≤ j
  · have hb : Nat.ble i j = true := by rw [ble_dec]; exact decide_eq_true hij
    rw [ite_eq_left hb] at h1
    have h2 := Nat.eq_of_beq_eq_true h1
    simp only [hij, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq]
    unfold coefBit
    rw [unpack_get _ _ hi, unpack_get _ _ hj]
    unfold coefN at h2
    rw [Orb.nIf_eq, pidx_eq] at h2
    by_cases he : i = j
    · subst he
      rw [ite_eq_left (Nat.beq_refl i)] at h2
      rw [ite_eq_left rfl]
      rw [bitN_eq, bitN_eq] at h2
      cases h3 : (rowP 22 C i).testBit i <;> cases h4 : t.testBit (pairIdx22 i i) <;>
        simp_all
    · have hb' : Nat.beq i j = false := by
        cases h' : Nat.beq i j
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') he
      rw [hb'] at h2
      rw [ite_eq_right he]
      simp only [Bool.false_eq_true, ↓reduceIte] at h2
      rw [bitN_eq, bitN_eq, bitN_eq] at h2
      cases h3 : (rowP 22 C i).testBit j <;> cases h4 : (rowP 22 C j).testBit i <;>
        cases h5 : t.testBit (pairIdx22 i j) <;> simp_all
  · simp [hij]

theorem pullK_sound_proved {A t t' : Nat} (h : pullK A t t' = true) :
    pullOK (unpack 22 22 A) t t' = true := by
  unfold pullOK
  rw [triP_eq, mulP_eq_proved, transP_eq, mulP_eq_proved]
  exact coefOK_of h

theorem offK_sound_proved {t t' : Nat} (h : offK t t' = true) : offDiagOK t t' = true := by
  unfold offK at h
  unfold offDiagOK
  rw [allLt_iff']
  intro i hi
  rw [allLt_iff']
  intro j hj
  have h1 := Orb.allN_iff.1 (Orb.allN_iff.1 h i hi) j hj
  rw [Orb.bIf_eq] at h1
  by_cases hij : i < j
  · have hb : Nat.blt i j = true := by rw [blt_dec]; exact decide_eq_true hij
    rw [ite_eq_left hb] at h1
    have h2 := Nat.eq_of_beq_eq_true h1
    rw [bitN_eq, bitN_eq, pidx_eq] at h2
    simp only [hij, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq]
    cases h3 : t.testBit (pairIdx22 i j) <;> cases h4 : t'.testBit (pairIdx22 i j) <;> simp_all
  · simp [hij]

theorem diagK_eq_proved (t : Nat) : diagK t = diagVec t := by
  apply Nat.eq_of_testBit_eq
  intro k
  unfold diagK diagVec
  rw [foldN_eq, orFold_testBit, testBit_ofBits]
  simp only [List.mem_range, beq_bitN, pidx_eq]

end Proofs

theorem mulP_eq (d X Y : Nat) : mulRows d (unpack d d X) (unpack d d Y) = unpack d d (mulP d X Y) :=
  mulP_eq_proved d X Y

theorem idP_eq (d : Nat) : idRows d = unpack d d (idP d) :=
  idP_eq_proved d

theorem powP_eq (d M e : Nat) : powRows d (unpack d d M) e = unpack d d (powP d M e) :=
  powP_eq_proved d M e

theorem unpack_packR {d : Nat} {f : Nat → Nat} (h : ∀ i < d, f i < 2 ^ d) :
    unpack d d (packR d f) = Array.ofFn (n := d) fun i => f i.val :=
  unpack_packR_proved h

theorem pullK_sound {A t t' : Nat} (h : pullK A t t' = true) : pullOK (unpack 22 22 A) t t' = true :=
  pullK_sound_proved h

theorem offK_sound {t t' : Nat} (h : offK t t' = true) : offDiagOK t t' = true :=
  offK_sound_proved h

theorem diagK_eq (t : Nat) : diagK t = diagVec t :=
  diagK_eq_proved t

end CFSG.KS.SporSch

end
