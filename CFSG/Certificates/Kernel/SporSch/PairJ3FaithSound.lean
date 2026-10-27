module

public import CFSG.Certificates.Kernel.SporSch.PairJ3InvSound
public import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Spor.HexText

public section

namespace CFSG.KS.SporSch.PF2

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Schreier.PairNative
open CFSG.Monster.B.Co2.Native CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Loop

@[expose] def HexRows (s : String) (d : Nat) (F : Nat → Nat) (lo cnt : Nat) : Prop :=
  s.toUTF8.size = d * cnt ∧ ∀ k < cnt, hexAt s.toUTF8 (d * k) d = F (lo + k)

private noncomputable def numK (L : List Char) (o : Nat) : Nat → Nat
  | 0 => 0
  | c + 1 => numK L o c * 16 + hexVK (L[o + c]!).toNat

private theorem strictB_hx (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_hx {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private theorem hexRun_zero {F : Nat → Nat} {e : Nat} : ∀ (L : List Char) (i j acc : Nat), 0 < j →
    hexRun 0 F e L i j acc = false
  | [], i, j, acc, hj => by
    change Bool.rec (motive := fun _ => Bool) false (Nat.beq j 0) (Nat.beq i e) = false
    cases Nat.beq i e
    · rfl
    · cases j with
      | zero => omega
      | succ j => rfl
  | ch :: L, i, j, acc, hj => by
    change strictB i (fun i => strictB (Char.toNat ch) fun c =>
      Bool.rec (motive := fun _ => Bool) false (strictB (Nat.add (Nat.mul acc 16) (hexVK c)) fun a =>
        strictB (Nat.succ j) fun j1 =>
          Bool.rec (motive := fun _ => Bool) (hexRun 0 F e L i j1 a)
            (Bool.rec (motive := fun _ => Bool) false (hexRun 0 F e L (Nat.succ i) 0 0)
              (Nat.beq a (F i))) (Nat.beq j1 0)) (Nat.blt c 128)) = false
    simp only [strictB_hx]
    cases Nat.blt (Char.toNat ch) 128
    · rfl
    · exact hexRun_zero L i (j + 1) _ (by omega)

private theorem hexRun_specK {d lo cnt : Nat} {F : Nat → Nat} {L : List Char} : ∀ r e t,
    L.length = d * e + t + r → t < d →
    hexRun d F (lo + cnt) (L.drop (d * e + t)) (lo + e) t (numK L (d * e) t) = true →
    L.length = d * cnt ∧ (∀ k, d * e + t ≤ k → k < L.length → (L[k]!).toNat < 128) ∧
      ∀ e', e ≤ e' → e' < cnt → numK L (d * e') d = F (lo + e')
  | 0, e, t, hl, _, h => by
    rw [List.drop_eq_nil_of_le (by omega)] at h
    change Bool.rec (motive := fun _ => Bool) false (Nat.beq t 0) (Nat.beq (lo + e) (lo + cnt))
      = true at h
    obtain ⟨h1, h2⟩ := bAnd_hx h
    have he : e = cnt := by have := Nat.eq_of_beq_eq_true h1; omega
    have ht : t = 0 := Nat.eq_of_beq_eq_true h2
    subst he ht
    exact ⟨by omega, fun k h1 h2 => by omega, fun e' h1 h2 => by omega⟩
  | r + 1, e, t, hl, htd, h => by
    have hp : d * e + t < L.length := by omega
    rw [List.drop_eq_getElem_cons hp] at h
    have hget : L[d * e + t]! = L[d * e + t] := getElem!_pos L _ hp
    change strictB (lo + e) (fun i => strictB (Char.toNat L[d * e + t]) fun c =>
      Bool.rec (motive := fun _ => Bool) false
        (strictB (Nat.add (Nat.mul (numK L (d * e) t) 16) (hexVK c)) fun a =>
        strictB (Nat.succ t) fun j1 =>
          Bool.rec (motive := fun _ => Bool)
            (hexRun d F (lo + cnt) (L.drop (d * e + t + 1)) i j1 a)
            (Bool.rec (motive := fun _ => Bool) false
              (hexRun d F (lo + cnt) (L.drop (d * e + t + 1)) (Nat.succ i) 0 0)
              (Nat.beq a (F i))) (Nat.beq j1 d)) (Nat.blt c 128)) = true at h
    simp only [strictB_hx] at h
    have hv : Nat.add (Nat.mul (numK L (d * e) t) 16) (hexVK (Char.toNat L[d * e + t])) =
        numK L (d * e) (t + 1) := by
      rw [numK, hget]
      rfl
    rw [hv] at h
    obtain ⟨hasc, h⟩ := bAnd_hx h
    have hasc : (L[d * e + t]!).toNat < 128 := by rw [hget]; exact Nat.blt_eq.mp hasc
    have hascK : ∀ k, d * e + t ≤ k → k < d * e + t + 1 → (L[k]!).toNat < 128 := by
      intro k h1 h2
      have : k = d * e + t := by omega
      rw [this]
      exact hasc
    cases h3 : Nat.beq (Nat.succ t) d <;> rw [h3] at h
    · have htd' : t + 1 < d := by
        have : t + 1 ≠ d := fun e => by
          change Nat.beq (t + 1) d = false at h3
          rw [e, Nat.beq_refl] at h3
          exact absurd h3 (by decide)
        omega
      have e1 : d * e + t + 1 = d * e + (t + 1) := by omega
      rw [e1] at h
      obtain ⟨a, b, c⟩ := hexRun_specK r e (t + 1) (by omega) htd' h
      refine ⟨a, fun k hk1 hk2 => ?_, c⟩
      rcases Nat.lt_or_ge k (d * e + t + 1) with hk | hk
      · exact hascK k hk1 hk
      · exact b k (by omega) hk2
    · have ht1 : t + 1 = d := Nat.eq_of_beq_eq_true h3
      obtain ⟨h4, h⟩ := bAnd_hx h
      have e1 : d * e + t + 1 = d * (e + 1) + 0 := by rw [Nat.mul_succ]; omega
      have e2 : Nat.succ (lo + e) = lo + (e + 1) := by omega
      rw [e1, e2] at h
      obtain ⟨a, b, c⟩ := hexRun_specK r (e + 1) 0 (by rw [Nat.mul_succ]; omega) (by omega) h
      refine ⟨a, fun k hk1 hk2 => ?_, fun e' he1 he2 => ?_⟩
      · rcases Nat.lt_or_ge k (d * e + t + 1) with hk | hk
        · exact hascK k hk1 hk
        · exact b k (by omega) hk2
      · rcases Nat.lt_or_ge e' (e + 1) with he | he
        · have he' : e' = e := by omega
          have h4' := Nat.eq_of_beq_eq_true h4
          rw [ht1] at h4'
          rw [he']
          exact h4'
        · exact c e' he he2

private theorem utf8_size_asciiK : ∀ cs : List Char,
    (∀ k < cs.length, (cs[k]!).toNat < 128) → cs.utf8Encode.size = cs.length
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c.toNat < 128 := by simpa using h 0 (by simp)
    rw [List.utf8Encode_cons, CFSG.KS.HexText.utf8_single hc, ByteArray.size_append,
      utf8_size_asciiK cs (fun k hk => by simpa using h (k + 1) (by simp; omega))]
    simp
    omega

private theorem hexVal_ofNat {x : Nat} (hx : x < 128) : hexVal (UInt8.ofNat x) = hexVK x := by
  have e : (UInt8.ofNat x).toNat = x := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  unfold hexVal hexVK
  rw [e]
  by_cases h : x < 58
  · rw [ite_eq_left h, show Nat.blt x 58 = true from Nat.blt_eq.mpr h]
    rfl
  · rw [ite_eq_right h, show Nat.blt x 58 = false from by
      cases e2 : Nat.blt x 58
      · rfl
      · exact absurd (Nat.blt_eq.mp e2) h]
    rfl

private theorem hexAt_numK {cs : List Char} (hasc : ∀ k < cs.length, (cs[k]!).toNat < 128)
    (o : Nat) : ∀ c, o + c ≤ cs.length → hexAt (String.ofList cs).toUTF8 o c = numK cs o c
  | 0, _ => rfl
  | c + 1, hc => by
    have hb : (String.ofList cs).toUTF8.get! (o + c) = UInt8.ofNat (cs[o + c]!).toNat := by
      rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
      exact CFSG.KS.HexText.utf8_get cs cs.length (fun k hk => ⟨hk, hasc k hk⟩) (o + c) (by omega)
    simp only [hexAt, numK]
    rw [hexAt_numK hasc o c (by omega), hb, hexVal_ofNat (hasc _ (by omega))]

theorem hexRowsK_sound {d : Nat} {F : Nat → Nat} {lo cnt : Nat} {cs : List Char}
    (h : hexRowsK d F lo cnt cs = true) : HexRows (String.ofList cs) d F lo cnt := by
  unfold hexRowsK at h
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    cases cs with
    | nil =>
      change Bool.rec (motive := fun _ => Bool) false (Nat.beq 0 0) (Nat.beq lo (lo + cnt)) = true
        at h
      obtain ⟨h1, -⟩ := bAnd_hx h
      have : cnt = 0 := by have := Nat.eq_of_beq_eq_true h1; omega
      subst this
      exact ⟨by simp, fun k hk => by omega⟩
    | cons ch L =>
      change strictB lo (fun i => strictB (Char.toNat ch) fun c =>
        Bool.rec (motive := fun _ => Bool) false (strictB (Nat.add (Nat.mul 0 16) (hexVK c)) fun a =>
          strictB (Nat.succ 0) fun j1 =>
            Bool.rec (motive := fun _ => Bool) (hexRun 0 F (lo + cnt) L i j1 a)
              (Bool.rec (motive := fun _ => Bool) false (hexRun 0 F (lo + cnt) L (Nat.succ i) 0 0)
                (Nat.beq a (F i))) (Nat.beq j1 0)) (Nat.blt c 128)) = true at h
      simp only [strictB_hx] at h
      cases e : Nat.blt (Char.toNat ch) 128 <;> rw [e] at h
      · exact absurd h Bool.false_ne_true
      · change hexRun 0 F (lo + cnt) L lo 1 _ = true at h
        rw [hexRun_zero L lo 1 _ (by omega)] at h
        exact absurd h Bool.false_ne_true
  · have h' : hexRun d F (lo + cnt) (cs.drop (d * 0 + 0)) (lo + 0) 0 (numK cs (d * 0) 0) = true := by
      rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero, List.drop_zero]
      exact h
    obtain ⟨hlen, hasc, hval⟩ := hexRun_specK (L := cs) cs.length 0 0 (by omega) hd h'
    have hasc' : ∀ k < cs.length, (cs[k]!).toNat < 128 := fun k hk => hasc k (by omega) hk
    have hsize : (String.ofList cs).toUTF8.size = cs.length := by
      rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
      exact utf8_size_asciiK cs hasc'
    refine ⟨by rw [hsize, hlen], fun k hk => ?_⟩
    rw [hexAt_numK hasc' (d * k) d (by rw [hlen, ← Nat.mul_succ]; exact Nat.mul_le_mul_left d hk)]
    exact hval k (Nat.zero_le k) hk

theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem testBit_orN_fields (w : Nat) (f : Nat → Nat) : ∀ n, (∀ i < n, f i < 2 ^ w) →
    ∀ j t, t < w → (orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)).testBit (j * w + t) =
      (decide (j < n) && (f j).testBit t) := by
  intro n
  induction n with
  | zero => intro _ j t _; exact Nat.zero_testBit _
  | succ n ih =>
    intro hf j t ht
    change (Nat.shiftLeft (f n) (w * n) ||| orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)).testBit
      (j * w + t) = _
    rw [Nat.testBit_or, ih (fun i hi => hf i (by omega)) j t ht]
    change ((f n <<< (w * n)).testBit (j * w + t) || _) = _
    rw [Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy j n with h | h | h
    · have : j * w + t < w * n := by nlinarith
      simp [h, show j < n + 1 by omega, show ¬ (w * n ≤ j * w + t) by omega]
    · subst h
      simp [Nat.mul_comm w j]
    · have h1 : w * n + w ≤ j * w := by nlinarith
      have hz : (f n).testBit (j * w + t - w * n) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf n (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hz, show ¬ j < n by omega, show ¬ j < n + 1 by omega]

theorem fget_orN (w n : Nat) (f : Nat → Nat) (hf : ∀ i < n, f i < 2 ^ w) (j : Nat) (hj : j < n) :
    fget (orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)) j w = f j := by
  apply Nat.eq_of_testBit_eq
  intro t
  change (((orN n fun i => Nat.shiftLeft (f i) (Nat.mul w i)) >>> (j * w)) &&& (pw2 w - 1)).testBit t
    = _
  rw [pw2_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases ht : t < w
  · rw [testBit_orN_fields w f n hf j t ht]
    simp [hj, ht]
  · simp only [ht, decide_false, Bool.and_false]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf j hj)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem rowF_lt (d M i : Nat) : rowF d M i < 2 ^ d := by
  change (M >>> (i * d)) &&& (pw2 d - 1) < 2 ^ d
  rw [pw2_eq]
  exact Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := d); omega)

theorem orN_lt (w : Nat) (g : Nat → Nat) : ∀ n, (∀ i < n, g i < 2 ^ w) → orN n g < 2 ^ w := by
  intro n
  induction n with
  | zero => intro _; exact Nat.two_pow_pos w
  | succ n ih =>
    intro h
    exact Nat.or_lt_two_pow (h n (by omega)) (ih fun i hi => h i (by omega))

theorem unpackP_get (d M i : Nat) (hi : i < d) : (unpackP d M)[i]?.getD 0 = rowF d M i := by
  simp [unpackP, hi]

theorem vmF_lt (d M v : Nat) : vmF d M v < 2 ^ d := by
  unfold vmF
  have key : ∀ n, Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Bool.rec (motive := fun _ => Nat)
      acc (Nat.xor (rowF d M k) acc) (bit v k)) n < 2 ^ d := by
    intro n
    induction n with
    | zero => exact Nat.two_pow_pos d
    | succ n ih =>
      change Bool.rec (motive := fun _ => Nat) _ (Nat.xor (rowF d M n) _) (bit v n) < 2 ^ d
      cases bit v n
      · exact ih
      · exact Nat.xor_lt_two_pow (rowF_lt d M n) ih
  exact key d

theorem vecMulN_eq (d M v : Nat) : vecMulN d (unpackP d M) v = vmF d M v := by
  unfold vecMulN vmF
  have key : ∀ n, n ≤ d → (List.range n).foldl (fun acc j => if v.testBit j then
      acc ^^^ ((unpackP d M)[j]?.getD 0) else acc) 0 =
      Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.xor (rowF d M k) acc) (bit v k)) n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        unpackP_get d M n (by omega)]
      change _ = Bool.rec (motive := fun _ => Nat) _ (Nat.xor (rowF d M n) _) (bit v n)
      rw [bit_eq]
      cases v.testBit n
      · rfl
      · exact Nat.xor_comm _ _
  exact key d le_rfl

theorem mulF_row (d A B i : Nat) (hi : i < d) : rowF d (mulF d A B) i = vmF d B (rowF d A i) := by
  unfold mulF
  rw [strictN_eq', strictN_eq']
  exact fget_orN d d (fun i => vmF d B (rowF d A i)) (fun _ _ => vmF_lt _ _ _) i hi

theorem mulRows_unpack (d A B : Nat) :
    mulRows d (unpackP d A) (unpackP d B) = unpackP d (mulF d A B) := by
  apply Array.ext (by simp [mulRows, unpackP])
  intro i h1 h2
  have hi : i < d := by simpa [unpackP] using h2
  simp only [mulRows, Array.getElem_map]
  have e : (unpackP d A)[i]'(by simp [unpackP]; omega) = rowF d A i := by simp [unpackP]
  rw [e, vecMulN_eq]
  simp only [unpackP, Array.getElem_ofFn]
  rw [mulF_row d A B i hi]

theorem mulF_sound {d A B C : Nat} (h : Nat.beq (mulF d A B) C = true) :
    mulRows d (unpackP d A) (unpackP d B) = unpackP d C := by
  rw [mulRows_unpack, Nat.eq_of_beq_eq_true h]

theorem idF_unpack (d : Nat) : unpackP d (idF d) = idRows d := by
  apply Array.ext (by simp [unpackP, idRows])
  intro i h1 h2
  have hi : i < d := by simpa [unpackP] using h1
  simp only [unpackP, idRows, Array.getElem_ofFn]
  have := fget_orN d d pw2 (fun j hj => by rw [pw2_eq]; exact Nat.pow_lt_pow_right (by norm_num) hj)
    i hi
  rw [rowF, idF, this, pw2]
  rfl

theorem mulF_id_sound {d A B : Nat} (h : Nat.beq (mulF d A B) (idF d) = true) :
    mulRows d (unpackP d A) (unpackP d B) = idRows d := by
  rw [mulF_sound h, idF_unpack]

@[expose] noncomputable def triRow (d z i : Nat) : Nat :=
  Nat.shiftLeft (Nat.land (Nat.shiftRight z (offP d i)) (Nat.sub (pw2 (Nat.sub d i)) 1)) i

theorem triRow_lt (d z i : Nat) (hi : i < d) : triRow d z i < 2 ^ d := by
  unfold triRow
  change ((z >>> offP d i) &&& (pw2 (d - i) - 1)) <<< i < 2 ^ d
  rw [pw2_eq, Nat.shiftLeft_eq]
  have h1 : (z >>> offP d i) &&& (2 ^ (d - i) - 1) < 2 ^ (d - i) :=
    Nat.and_lt_two_pow _ (by have := Nat.one_le_two_pow (n := d - i); omega)
  calc _ < 2 ^ (d - i) * 2 ^ i := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos i)
    _ = 2 ^ d := by rw [← Nat.pow_add]; congr 1; omega

theorem triP_eq (d z : Nat) : triP d z = orN d fun i => Nat.shiftLeft (triRow d z i) (Nat.mul d i) := by
  unfold triP triRow
  congr 1
  funext i
  exact Nat.shiftLeft_add _ i (d * i)

theorem triP_row (d z i : Nat) (hi : i < d) : rowF d (triP d z) i = triRow d z i := by
  rw [rowF, triP_eq]
  exact fget_orN d d _ (fun j hj => triRow_lt d z j hj) i hi

theorem offP_eq (d i : Nat) : offP d i = pairIdx d i i := by
  unfold offP pairIdx
  rw [Nat.sub_self, Nat.add_zero]
  rfl

theorem triRows_eq (d z : Nat) : triRowsZ d z = unpackP d (triP d z) := by
  apply Array.ext (by simp [triRowsZ, unpackP])
  intro i h1 h2
  have hi : i < d := by simpa [unpackP] using h2
  simp only [triRowsZ, unpackP, Array.getElem_ofFn]
  rw [triP_row d z i hi, triRow, offP_eq, pw2_eq]
  rfl

theorem packRows_eq (d U : Nat) : packRowsZ d (unpackP d U) = packP d U := by
  unfold packRowsZ packP
  have key : ∀ n, n ≤ d → (List.range n).foldl (fun acc i =>
      acc ||| (((unpackP d U)[i]?.getD 0 >>> i) <<< pairIdx d i i)) 0 =
      orN n fun i => Nat.shiftLeft (Nat.shiftRight (rowF d U i) i) (offP d i) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        unpackP_get d U n (by omega), ← offP_eq]
      exact Nat.lor_comm _ _
  exact key d le_rfl

theorem packK_sound {d z : Nat} (h : Nat.beq (packP d (triP d z)) z = true) :
    packRowsZ d (triRowsZ d z) = z := by
  rw [triRows_eq, packRows_eq, Nat.eq_of_beq_eq_true h]

theorem rowF_xor (d U V j : Nat) : rowF d (Nat.xor U V) j = rowF d U j ^^^ rowF d V j := by
  apply Nat.eq_of_testBit_eq
  intro t
  change (((U ^^^ V) >>> (j * d)) &&& (pw2 d - 1)).testBit t =
    (((U >>> (j * d)) &&& (pw2 d - 1)) ^^^ ((V >>> (j * d)) &&& (pw2 d - 1))).testBit t
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor]
  cases U.testBit (j * d + t) <;> cases V.testBit (j * d + t) <;> cases (pw2 d - 1).testBit t <;> rfl

theorem colB_lt (d A j : Nat) : colB d A j < 2 ^ d := by
  unfold colB
  apply orN_lt
  intro i hi
  change (Bool.rec (motive := fun _ => Nat) 0 1 (bit (rowF d A i) j)) <<< i < 2 ^ d
  cases bit (rowF d A i) j
  · change 0 <<< i < 2 ^ d
    rw [Nat.zero_shiftLeft]
    exact Nat.two_pow_pos d
  · rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) hi

theorem ofBits_eq (d A j : Nat) :
    ofBits d (fun i => ((unpackP d A)[i]?.getD 0).testBit j) = colB d A j := by
  unfold ofBits colB
  have key : ∀ n, n ≤ d → (List.range n).foldl (fun acc i =>
      if ((unpackP d A)[i]?.getD 0).testBit j then acc ||| (1 <<< i) else acc) 0 =
      orN n fun i => Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (bit (rowF d A i) j)) i := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        unpackP_get d A n (by omega)]
      change _ = (Bool.rec (motive := fun _ => Nat) 0 1 (bit (rowF d A n) j)) <<< n ||| _
      rw [bit_eq]
      cases h : (rowF d A n).testBit j
      · simp only [Bool.false_eq_true, ite_false]
        rw [Nat.zero_shiftLeft, Nat.zero_or]
        rfl
      · simp only [ite_true]
        change _ ||| (1 <<< n) = (1 <<< n) ||| _
        exact Nat.lor_comm _ _
  exact key d le_rfl

theorem trB_row (d A j : Nat) (hj : j < d) : rowF d (trB d A) j = colB d A j := by
  rw [rowF, trB]
  exact fget_orN d d _ (fun i _ => colB_lt d A i) j hj

theorem polarK_sound {d z M : Nat} (h : Nat.beq (polarP d z) M = true) :
    polarRowsZ d z = unpackP d M := by
  rw [← Nat.eq_of_beq_eq_true h, polarP, strictN_eq', polarRowsZ, triRows_eq]
  apply Array.ext (by simp [addRows, unpackP, transposeRows])
  intro j h1 h2
  have hj : j < d := by simpa [unpackP] using h2
  simp only [addRows, Array.getElem_zipWith, transposeRows, Array.getElem_ofFn, unpackP]
  rw [rowF_xor, trB_row d _ j hj, ← ofBits_eq]
  simp only [unpackP]

theorem get!_data (x : ByteArray) (i : Nat) : x.get! i = x.data[i]! := by
  cases x
  rfl

theorem get!_append_left (x y : ByteArray) (i : Nat) (h : i < x.size) :
    (x ++ y).get! i = x.get! i := by
  rw [get!_data, get!_data, ByteArray.data_append]
  have ha : i < x.data.size := by simpa using h
  rw [getElem!_pos (x.data ++ y.data) i (by simp; omega), getElem!_pos x.data i ha,
    Array.getElem_append_left]

theorem get!_append_right (x y : ByteArray) (i : Nat) : (x ++ y).get! (x.size + i) = y.get! i := by
  rw [get!_data, get!_data, ByteArray.data_append, ← ByteArray.size_data]
  generalize x.data = a
  generalize y.data = b
  by_cases hb : i < b.size
  · rw [getElem!_pos (a ++ b) _ (by simp; omega), getElem!_pos b i hb, Array.getElem_append_right]
    · congr 1
      omega
    · omega
  · rw [getElem!_neg (a ++ b) _ (by simp; omega), getElem!_neg b i hb]

theorem hexAt_append_left (x y : ByteArray) (o : Nat) :
    ∀ w, o + w ≤ x.size → hexAt (x ++ y) o w = hexAt x o w := by
  intro w
  induction w with
  | zero => intro _; rfl
  | succ w ih =>
    intro h
    simp only [hexAt]
    rw [ih (by omega), get!_append_left _ _ _ (by omega)]

theorem hexAt_append_right (x y : ByteArray) (o : Nat) :
    ∀ w, hexAt (x ++ y) (x.size + o) w = hexAt y o w := by
  intro w
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [hexAt]
    rw [ih, Nat.add_assoc, get!_append_right]

theorem toUTF8_append (s t : String) : (s ++ t).toUTF8 = s.toUTF8 ++ t.toUTF8 := by
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append]

theorem HexRows.append {s t : String} {d : Nat} {F : Nat → Nat} {lo n m : Nat}
    (hs : HexRows s d F lo n) (ht : HexRows t d F (lo + n) m) : HexRows (s ++ t) d F lo (n + m) := by
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ht1, ht2⟩ := ht
  refine ⟨by rw [toUTF8_append, ByteArray.size_append, hs1, ht1, Nat.mul_add], ?_⟩
  intro k hk
  rw [toUTF8_append]
  by_cases hkn : k < n
  · rw [hexAt_append_left _ _ _ _ (by rw [hs1]; nlinarith), hs2 k hkn]
  · have e : d * k = s.toUTF8.size + d * (k - n) := by
      rw [hs1, ← Nat.mul_add]
      congr 1
      omega
    rw [e, hexAt_append_right, ht2 (k - n) (by omega)]
    congr 1
    omega

theorem HexRows.of_eq {s : String} {cs : List Char} {d : Nat} {F : Nat → Nat} {lo cnt : Nat}
    (he : s = String.ofList cs) (h : hexRowsK d F lo cnt cs = true) : HexRows s d F lo cnt :=
  he ▸ hexRowsK_sound h

theorem rowsGo_sound (d M : Nat) : ∀ (L : List Nat) (i : Nat), rowsGo d M L i = true →
    L = (List.range' i L.length).map (rowF d M) ∧ i + L.length = d := by
  intro L
  induction L with
  | nil => intro i h; exact ⟨rfl, by simpa using Nat.eq_of_beq_eq_true h⟩
  | cons x L ih =>
    intro i h
    change Bool.rec (motive := fun _ => Bool) false (rowsGo d M L (i + 1)) (Nat.beq x (rowF d M i))
      = true at h
    cases h1 : Nat.beq x (rowF d M i) <;> rw [h1] at h
    · exact absurd h Bool.false_ne_true
    · obtain ⟨e1, e2⟩ := ih (i + 1) h
      refine ⟨?_, by simp; omega⟩
      rw [List.length_cons, List.range'_succ, List.map_cons, ← e1, Nat.eq_of_beq_eq_true h1]

theorem rowsEqK_sound {d M : Nat} {L : List Nat} (h : rowsEqK d M L = true) :
    L.toArray = unpackP d M := by
  change Bool.rec (motive := fun _ => Bool) false (rowsGo d M L 0) (Nat.blt M (pw2 (d * d))) = true
    at h
  cases h1 : Nat.blt M (pw2 (d * d)) <;> rw [h1] at h
  · exact absurd h Bool.false_ne_true
  · obtain ⟨e1, e2⟩ := rowsGo_sound d M L 0 h
    apply Array.ext'
    rw [List.toList_toArray, e1]
    apply List.ext_getElem (by simp [unpackP]; omega)
    intro j h1 h2
    simp [unpackP]

theorem parLt_of_forall {n chunks : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    parLt n chunks p = true := by
  unfold parLt
  simp only [List.all_map, List.all_eq_true, Function.comp_apply]
  intro c _
  change allLt (n / chunks + 1) (fun k => !decide (c * (n / chunks + 1) + k < n) ||
    p (c * (n / chunks + 1) + k)) = true
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro k _
  by_cases hk : c * (n / chunks + 1) + k < n
  · simp [h _ hk]
  · simp [hk]

theorem strictInc_of (l : List Nat) (h : ∀ i (hi : i + 1 < l.length), l[i] < l[i + 1]) :
    strictInc l = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      have h0 := h 0 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0
      simp only [strictInc, decide_eq_true h0, Bool.true_and]
      refine ih fun i hi => ?_
      have := h (i + 1) (by simp at hi ⊢; omega)
      simpa using this

theorem sorted_strictInc {n : Nat} {g F σ τ : Nat → Nat} (hg : ∀ r < n, g r = F r)
    (hs : ∀ i, i + 1 < n → F (σ i) < F (σ (i + 1))) (hp : ∀ i < n, σ i < n ∧ τ (σ i) = i) :
    strictInc ((List.range n).map g).mergeSort = true := by
  set M := (List.range n).map (fun i => F (σ i)) with hM
  have hadj : ∀ i (hi : i + 1 < M.length), M[i] < M[i + 1] := by
    intro i hi
    simp only [hM, List.length_map, List.length_range] at hi
    simp only [hM, List.getElem_map, List.getElem_range]
    exact hs i hi
  have hpair : M.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    induction j, hij using Nat.le_induction with
    | base => exact hadj i hj
    | succ j hij ih => exact lt_trans (ih (by omega)) (hadj j hj)
  have hperm : List.Perm M ((List.range n).map g) := by
    have e : (List.range n).map g = (List.range n).map F :=
      List.map_congr_left fun r hr => hg r (List.mem_range.1 hr)
    have hc : (fun i => F (σ i)) = F ∘ σ := rfl
    rw [e, hM, hc, ← List.map_map]
    apply List.Perm.map
    have hnd : ((List.range n).map σ).Nodup := by
      apply List.Nodup.map_on _ List.nodup_range
      intro x hx y hy hxy
      rw [← (hp x (List.mem_range.1 hx)).2, ← (hp y (List.mem_range.1 hy)).2, hxy]
    apply List.Subperm.perm_of_length_le (List.Nodup.subperm hnd _) (by simp)
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hp i (List.mem_range.1 hi)).1
  have heq : ((List.range n).map g).mergeSort = M := by
    apply List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b))
    · intro a b _ _ h1 h2
      simp only [decide_eq_true_eq] at h1 h2
      omega
    · exact List.pairwise_mergeSort (fun a b c h1 h2 => by simp_all; omega)
        (fun a b => by simp; omega) _
    · exact hpair.imp fun h => by simp; omega
    · exact (List.mergeSort_perm _ _).trans hperm.symm
  rw [heq]
  exact strictInc_of M hadj

private def pk (s : Nat) (u : Nat → Nat) (k : Nat) : Nat :=
  ∑ i ∈ Finset.range k, u i * 2 ^ (s * i)

private theorem pk_succ (s : Nat) (u : Nat → Nat) (k : Nat) :
    pk s u (k + 1) = pk s u k + u k * 2 ^ (s * k) := by
  unfold pk
  rw [Finset.sum_range_succ]

private theorem pk_lt {s : Nat} {u : Nat → Nat} (hu : ∀ i, u i < 2 ^ s) : ∀ k, pk s u k < 2 ^ (s * k)
  | 0 => by simp [pk]
  | k + 1 => by
    rw [pk_succ]
    have h1 := pk_lt hu k
    have h2 : u k + 1 ≤ 2 ^ s := hu k
    calc pk s u k + u k * 2 ^ (s * k) < 2 ^ (s * k) + u k * 2 ^ (s * k) := by omega
      _ = (u k + 1) * 2 ^ (s * k) := by ring
      _ ≤ 2 ^ s * 2 ^ (s * k) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (s * (k + 1)) := by rw [← Nat.pow_add]; congr 1; ring

private theorem pk_bit {s : Nat} {u : Nat → Nat} (hs : 0 < s) (hu : ∀ i, u i < 2 ^ s) :
    ∀ k p, (pk s u k).testBit p = (decide (p / s < k) && (u (p / s)).testBit (p % s))
  | 0, p => by simp [pk]
  | k + 1, p => by
    rw [pk_succ, ← Nat.shiftLeft_eq, Nat.add_comm,
      Nat.shiftLeft_add_eq_or_of_lt (pk_lt hu k), Nat.testBit_or, Nat.testBit_shiftLeft,
      pk_bit hs hu k p]
    rcases Nat.lt_or_ge p (s * k) with hp | hp
    · have hq : p / s < k := (Nat.div_lt_iff_lt_mul hs).2 (by rw [Nat.mul_comm]; exact hp)
      simp [hq, show p / s < k + 1 by omega, show ¬ s * k ≤ p by omega]
    · have hq : ¬ p / s < k := by
        rw [not_lt, Nat.le_div_iff_mul_le hs]
        rw [Nat.mul_comm]
        exact hp
      simp only [hq, decide_false, Bool.false_and, Bool.or_false, ge_iff_le, hp, decide_true,
        Bool.true_and]
      rcases Nat.lt_or_ge p (s * (k + 1)) with hp2 | hp2
      · have he : p / s = k := by
          apply Nat.div_eq_of_lt_le
          · rw [Nat.mul_comm]; exact hp
          · have : s * (k + 1) = s * k + s := Nat.mul_succ s k
            rw [Nat.mul_comm]; omega
        have hm : p % s = p - s * k := by
          have := Nat.div_add_mod p s
          rw [he] at this
          omega
        simp [he, hm]
      · have hq2 : ¬ p / s < k + 1 := by
          rw [not_lt, Nat.le_div_iff_mul_le hs, Nat.mul_comm]
          exact hp2
        simp only [hq2, decide_false, Bool.false_and]
        apply Nat.testBit_lt_two_pow
        calc u k < 2 ^ s := hu k
          _ ≤ 2 ^ (p - s * k) := Nat.pow_le_pow_right (by norm_num) (by
              rw [Nat.mul_succ] at hp2; omega)

private theorem repU_eq {s : Nat} (hs : 0 < s) (k : Nat) : repU s k = pk s (fun _ => 1) k := by
  have key : ∀ k, pk s (fun _ => 1) k * (2 ^ s - 1) = 2 ^ (s * k) - 1 := by
    intro k
    induction k with
    | zero => simp [pk]
    | succ k ih =>
      rw [pk_succ, Nat.add_mul, ih]
      have h1 : 1 ≤ 2 ^ (s * k) := Nat.one_le_two_pow
      have h2 : 2 ≤ 2 ^ s := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
      have e : 2 ^ (s * (k + 1)) = 2 ^ (s * k) * 2 ^ s := by rw [← Nat.pow_add]; ring_nf
      rw [e]
      obtain ⟨a, ha⟩ : ∃ a, 2 ^ s = a + 2 := ⟨2 ^ s - 2, by omega⟩
      obtain ⟨t, ht⟩ : ∃ t, 2 ^ (s * k) = t + 1 := ⟨2 ^ (s * k) - 1, by omega⟩
      rw [ha, ht]
      simp only [Nat.add_sub_cancel, one_mul]
      rw [show a + 2 - 1 = a + 1 by omega, show (t + 1) * (a + 2) - 1 = t * (a + 2) + (a + 1) by
        rw [Nat.add_mul]; omega]
      ring
  unfold repU
  change (1 <<< (s * k) - 1) / (1 <<< s - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
  have hpos : 0 < 2 ^ s - 1 := by
    have : 2 ≤ 2 ^ s := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    omega
  exact Nat.div_eq_of_eq_mul_left hpos (key k).symm

private theorem pk_mul (s : Nat) (u : Nat → Nat) (y k : Nat) :
    y * pk s u k = pk s (fun i => y * u i) k := by
  unfold pk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private theorem repU_bit {s : Nat} (hs : 0 < s) (k p : Nat) :
    (repU s k).testBit p = (decide (p / s < k) && decide (p % s = 0)) := by
  rw [repU_eq hs, pk_bit hs (fun _ => Nat.one_lt_two_pow (by omega)) k p]
  cases p % s with
  | zero => simp
  | succ j => simp [Nat.testBit_succ]

private theorem mul_repU_bit {s y : Nat} (hs : 0 < s) (hy : y < 2 ^ s) (k p : Nat) :
    (y * repU s k).testBit p = (decide (p / s < k) && y.testBit (p % s)) := by
  rw [repU_eq hs, pk_mul, pk_bit hs (fun _ => by simpa using hy) k p]
  simp

private theorem rowF_bit (d M i j : Nat) :
    (rowF d M i).testBit j = (decide (j < d) && M.testBit (i * d + j)) := by
  change ((M >>> (i * d)) &&& (pw2 d - 1)).testBit j = _
  rw [pw2_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

private theorem orN_bit (f : Nat → Nat) (p : Nat) : ∀ n,
    (orN n f).testBit p = true ↔ ∃ i < n, (f i).testBit p = true
  | 0 => by simp [orN]
  | n + 1 => by
    change ((f n) ||| (orN n f)).testBit p = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, orN_bit f p n]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

private theorem colB_bit (d A j t : Nat) :
    (colB d A j).testBit t = true ↔ t < d ∧ (rowF d A t).testBit j = true := by
  unfold colB
  rw [orN_bit]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [bit_eq] at h
    cases hb : (rowF d A i).testBit j <;> rw [hb] at h
    · change (0 <<< i).testBit t = true at h
      simp at h
    · change (1 <<< i).testBit t = true at h
      rw [Nat.testBit_shiftLeft] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have : t - i = 0 := by
        by_contra hne
        have h2 := h.2
        rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hne)] at h2
        exact absurd h2 (by decide)
      have : t = i := by omega
      subst this
      exact ⟨hi, hb⟩
  · rintro ⟨ht, h⟩
    refine ⟨t, ht, ?_⟩
    rw [bit_eq, h]
    change (1 <<< t).testBit t = true
    rw [Nat.testBit_shiftLeft]
    simp

private theorem trB_bit {d : Nat} (hd : 0 < d) (A q : Nat) :
    (trB d A).testBit q = true ↔ q < d * d ∧ A.testBit (q % d * d + q / d) = true := by
  have hq := Nat.div_add_mod q d
  have e : q = q / d * d + q % d := by rw [Nat.mul_comm]; omega
  rw [e, trB, testBit_orN_fields d (fun j => colB d A j) d (fun j _ => colB_lt d A j) (q / d)
    (q % d) (Nat.mod_lt q hd)]
  rw [← e]
  rw [Bool.and_eq_true, decide_eq_true_eq, colB_bit, rowF_bit]
  have hm := Nat.mod_lt q hd
  simp only [hm, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc q = q / d * d + q % d := e
        _ < q / d * d + d := by omega
        _ = (q / d + 1) * d := by ring
        _ ≤ d * d := by rw [Nat.mul_comm d d]; exact Nat.mul_le_mul_right d h1
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact h2.2
  · rintro ⟨h1, h2⟩
    have hj : q / d < d := (Nat.div_lt_iff_lt_mul hd).2 h1
    exact ⟨hj, by simp [hj, h2]⟩

private theorem spread_bit {d r : Nat} (hd : 2 ≤ d) (hr : r < 2 ^ d) (p : Nat) :
    ((Nat.land (Nat.mul r (repU (2 * (d - 1)) ((d + 1) / 2))) (repU (2 * d) ((d + 1) / 2))) |||
      (Nat.land (Nat.mul r (Nat.shiftLeft (repU (2 * (d - 1)) (d / 2)) (d - 1)))
        (Nat.shiftLeft (repU (2 * d) (d / 2)) d))).testBit p = true ↔
      ∃ j < d, p = d * j ∧ r.testBit j = true := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hs : 2 * (e + 2 - 1) = 2 * e + 2 := by omega
  have hd1 : e + 2 - 1 = e + 1 := by omega
  rw [hs, hd1]
  have hrs : r < 2 ^ (2 * e + 2) := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) (by omega))
  have e1 : Nat.mul r (Nat.shiftLeft (repU (2 * e + 2) ((e + 2) / 2)) (e + 1)) =
      (r * repU (2 * e + 2) ((e + 2) / 2)) <<< (e + 1) := by
    change r * (repU (2 * e + 2) ((e + 2) / 2) <<< (e + 1)) = _
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_assoc]
  rw [e1]
  change (((r * repU (2 * e + 2) ((e + 2 + 1) / 2)) &&& repU (2 * (e + 2)) ((e + 2 + 1) / 2)) |||
      (((r * repU (2 * e + 2) ((e + 2) / 2)) <<< (e + 1)) &&&
        (repU (2 * (e + 2)) ((e + 2) / 2) <<< (e + 2)))).testBit p = true ↔ _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    mul_repU_bit (by omega) hrs, mul_repU_bit (by omega) hrs, repU_bit (by omega), repU_bit (by omega)]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  have hs0 : 0 < 2 * e + 2 := by omega
  have hd0 : 0 < 2 * (e + 2) := by omega
  constructor
  · rintro (⟨⟨-, hb⟩, hq2, hm⟩ | ⟨⟨-, -, hb⟩, h2, hq2, hm⟩)
    · obtain ⟨m, hmdef⟩ : ∃ m, m = p / (2 * (e + 2)) := ⟨_, rfl⟩
      rw [← hmdef] at hq2
      have hp : p = 2 * m + (2 * e + 2) * m := by
        have := Nat.div_add_mod p (2 * (e + 2))
        rw [hm, ← hmdef] at this
        rw [← this]
        ring
      have h2m : 2 * m < 2 * e + 2 := by omega
      have hmod : p % (2 * e + 2) = 2 * m := by
        rw [hp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2m]
      rw [hmod] at hb
      exact ⟨2 * m, by omega, by rw [hp]; ring, hb⟩
    · obtain ⟨m, hmdef⟩ : ∃ m, m = (p - (e + 2)) / (2 * (e + 2)) := ⟨_, rfl⟩
      rw [← hmdef] at hq2
      have hp' : p - (e + 2) = 2 * (e + 2) * m := by
        have := Nat.div_add_mod (p - (e + 2)) (2 * (e + 2))
        rw [hm, ← hmdef] at this
        omega
      have hp : p = (e + 2) * (2 * m + 1) := by
        have : p = p - (e + 2) + (e + 2) := by omega
        rw [this, hp']
        ring
      have h2m : 2 * m + 1 < 2 * e + 2 := by omega
      have hq : p - (e + 1) = (2 * m + 1) + (2 * e + 2) * m := by
        apply Nat.sub_eq_of_eq_add
        rw [hp]
        ring
      have hmod : (p - (e + 1)) % (2 * e + 2) = 2 * m + 1 := by
        rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2m]
      rw [hmod] at hb
      exact ⟨2 * m + 1, by omega, hp, hb⟩
  · rintro ⟨j, hj, hp, hb⟩
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
    · left
      have hp1 : p = 2 * m + (2 * e + 2) * m := by rw [hp]; ring
      have hp2 : p = 2 * (e + 2) * m := by rw [hp]; ring
      have h2m : 2 * m < 2 * e + 2 := by omega
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [hp1, Nat.add_mul_div_left _ _ hs0, Nat.div_eq_of_lt h2m]
        omega
      · rw [hp1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2m]
        exact hb
      · rw [hp2, Nat.mul_div_cancel_left _ hd0]
        omega
      · rw [hp2, Nat.mul_mod_right]
    · right
      have h2m : 2 * m + 1 < 2 * e + 2 := by omega
      have hq : p - (e + 1) = (2 * m + 1) + (2 * e + 2) * m := by
        apply Nat.sub_eq_of_eq_add
        rw [hp]
        ring
      have hq' : p - (e + 2) = 2 * (e + 2) * m := by
        apply Nat.sub_eq_of_eq_add
        rw [hp]
        ring
      have hpe : e + 2 ≤ p := by
        rw [hp]
        nlinarith
      refine ⟨⟨by omega, ?_, ?_⟩, hpe, ?_, ?_⟩
      · rw [hq, Nat.add_mul_div_left _ _ hs0, Nat.div_eq_of_lt h2m]
        omega
      · rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2m]
        exact hb
      · rw [hq', Nat.mul_div_cancel_left _ hd0]
        omega
      · rw [hq', Nat.mul_mod_right]

private theorem divmod_uniq {d a b c e : Nat} (hb : b < d) (he : e < d) (h : a * d + b = d * c + e) :
    a = c ∧ b = e := by
  have hd : 0 < d := by omega
  have h1 : (a * d + b) / d = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hb, Nat.zero_add]
  have h2 : (d * c + e) / d = c := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt he, Nat.zero_add]
  have h3 : (a * d + b) % d = b := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have h4 : (d * c + e) % d = e := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

private theorem trP_row {d : Nat} (hd : 2 ≤ d) (A j : Nat) (hj : j < d) :
    rowF d (trP d A) j = colB d A j := by
  have hsp : ∀ p, (trP d A).testBit p = true ↔
      ∃ i < d, ∃ k < d, p = d * k + i ∧ (rowF d A i).testBit k = true := by
    intro p
    unfold trP
    rw [strictN_eq', strictN_eq', strictN_eq', strictN_eq', orN_bit]
    constructor
    · rintro ⟨i, hi, h⟩
      change (Nat.shiftLeft _ i).testBit p = true at h
      rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hip, h⟩ := h
      have h' := (spread_bit hd (rowF_lt d A i) (p - i)).1 h
      obtain ⟨k, hk, hpk, hb⟩ := h'
      exact ⟨i, hi, k, hk, by omega, hb⟩
    · rintro ⟨i, hi, k, hk, hp, hb⟩
      refine ⟨i, hi, ?_⟩
      change (Nat.shiftLeft _ i).testBit p = true
      rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, (spread_bit hd (rowF_lt d A i) (p - i)).2 ⟨k, hk, by omega, hb⟩⟩
  apply Nat.eq_of_testBit_eq
  intro t
  rw [rowF_bit]
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, decide_eq_true_eq, hsp, colB_bit]
  constructor
  · rintro ⟨ht, i, hi, k, hk, hp, hb⟩
    obtain ⟨e1, e2⟩ := divmod_uniq ht hi hp
    subst e1 e2
    exact ⟨ht, hb⟩
  · rintro ⟨ht, hb⟩
    exact ⟨ht, t, ht, j, hj, by ring, hb⟩

private theorem trP_unpack {d : Nat} (hd : 2 ≤ d) (A : Nat) :
    transposeRows d (unpackP d A) = unpackP d (trP d A) := by
  apply Array.ext (by simp [unpackP, transposeRows])
  intro j h1 h2
  have hj : j < d := by simpa [unpackP] using h2
  simp only [transposeRows, Array.getElem_ofFn, unpackP]
  rw [trP_row hd A j hj, ← ofBits_eq]
  simp only [unpackP]

private theorem xor_eqK (a b : Nat) : Nat.xor a b = a ^^^ b := rfl

private theorem mterm_bit {d : Nat} (hd : 0 < d) (A B k p : Nat) :
    (Nat.land (Nat.mul (Nat.land (Nat.shiftRight A k) (repU d d)) (Nat.sub (pw2 d) 1))
      (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul d k)) (Nat.sub (pw2 d) 1)) (repU d d))).testBit p =
      (decide (p / d < d) && A.testBit (d * (p / d) + k) && B.testBit (d * k + p % d)) := by
  have hrm : Nat.sub (pw2 d) 1 = 2 ^ d - 1 := by rw [← pw2_eq]; rfl
  have hrm_lt : 2 ^ d - 1 < 2 ^ d := by have := Nat.one_le_two_pow (n := d); omega
  set a : Nat → Nat := fun m => if A.testBit (d * m + k) then 1 else 0 with ha
  have hX : Nat.land (Nat.shiftRight A k) (repU d d) = pk d a d := by
    apply Nat.eq_of_testBit_eq
    intro p
    change ((A >>> k) &&& repU d d).testBit p = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, repU_bit hd,
      pk_bit hd (fun m => by simp only [ha]; split <;> simp [Nat.one_lt_two_pow (by omega : d ≠ 0)])]
    simp only [ha]
    by_cases hm : p % d = 0
    · have hp : k + p = d * (p / d) + k := by have := Nat.div_add_mod p d; omega
      rw [hp]
      split <;> rename_i hA <;> simp [hm, hA]
    · split <;> simp [hm, Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hm)]
  have hr : Nat.land (Nat.shiftRight B (Nat.mul d k)) (Nat.sub (pw2 d) 1) < 2 ^ d := by
    rw [hrm]
    exact Nat.and_lt_two_pow _ hrm_lt
  rw [hX, hrm]
  change ((pk d a d * (2 ^ d - 1)) &&& (((B >>> (d * k)) &&& (2 ^ d - 1)) * repU d d)).testBit p = _
  rw [Nat.testBit_and, Nat.mul_comm (pk d a d), pk_mul, Nat.mul_comm _ (repU d d)]
  rw [Nat.mul_comm (repU d d)]
  rw [pk_bit hd (fun m => by simp only [ha]; split <;> simp [hrm_lt]),
    mul_repU_bit hd (Nat.and_lt_two_pow _ hrm_lt)]
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  have hm := Nat.mod_lt p hd
  simp only [ha]
  split <;> rename_i hA <;> simp [hm, hA]

private theorem mulP_row {d : Nat} (hd : 0 < d) (A B q : Nat) (hq : q < d) :
    rowF d (mulP d A B) q = vmF d B (rowF d A q) := by
  have key : ∀ K, K ≤ d → ∀ t < d,
      (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => mstepP d (repU d d) (Nat.sub (pw2 d) 1) A B acc k)
        K).testBit (q * d + t) =
      (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.xor (rowF d B k) acc) (bit (rowF d A q) k)) K).testBit t := by
    intro K
    induction K with
    | zero => intro _ t _; simp
    | succ K ih =>
      intro hK t ht
      change (Nat.xor _ _).testBit (q * d + t) =
        (Bool.rec (motive := fun _ => Nat) _ (Nat.xor (rowF d B K) _) (bit (rowF d A q) K)).testBit t
      have hdiv : (q * d + t) / d = q := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt ht, Nat.zero_add]
      have hmod : (q * d + t) % d = t := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
      rw [xor_eqK, Nat.testBit_xor, ih (by omega) t ht]
      rw [mterm_bit hd, hdiv, hmod, bit_eq, rowF_bit]
      have hK' : K < d := by omega
      simp only [hK', hq, decide_true, Bool.true_and]
      have e1 : d * q + K = q * d + K := by ring
      rw [e1]
      cases A.testBit (q * d + K)
      · simp
      · change _ = (Nat.xor (rowF d B K) _).testBit t
        rw [xor_eqK, Nat.testBit_xor, rowF_bit]
        simp only [ht, decide_true, Bool.true_and]
        have e2 : d * K + t = K * d + t := by ring
        rw [e2, Bool.xor_comm]
  apply Nat.eq_of_testBit_eq
  intro t
  rw [rowF_bit]
  by_cases ht : t < d
  · simp only [ht, decide_true, Bool.true_and]
    unfold mulP
    rw [strictN_eq', strictN_eq']
    exact key d le_rfl t ht
  · simp only [ht, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (vmF_lt d B _)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

private theorem mulP_unpack {d : Nat} (hd : 0 < d) (A B : Nat) :
    mulRows d (unpackP d A) (unpackP d B) = unpackP d (mulP d A B) := by
  rw [mulRows_unpack]
  apply Array.ext (by simp [unpackP])
  intro i h1 h2
  have hi : i < d := by simpa [unpackP] using h2
  simp only [unpackP, Array.getElem_ofFn]
  rw [mulF_row d A B i hi, mulP_row hd A B i hi]

private theorem one_bit (k : Nat) : (1 : Nat).testBit k = decide (k = 0) := by
  cases k with
  | zero => simp
  | succ j => simp [Nat.testBit_succ]

private theorem diag_bit {d i j : Nat} (hi : i < d) (hj : j < d) :
    (repU (d + 1) d).testBit (i * d + j) = decide (j = i) := by
  rw [repU_bit (by omega)]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hp := Nat.div_add_mod (i * d + j) (d + 1)
    rw [h2, Nat.add_zero] at hp
    have e : i * d + j = d * ((i * d + j) / (d + 1)) + (i * d + j) / (d + 1) := by
      conv_lhs => rw [← hp]
      ring
    exact ((divmod_uniq hj h1 e).2).trans ((divmod_uniq hj h1 e).1).symm
  · rintro rfl
    have e : j * d + j = (d + 1) * j := by ring
    rw [e, Nat.mul_div_cancel_left _ (by omega), Nat.mul_mod_right]
    exact ⟨hj, rfl⟩

private theorem su_eq (d : Nat) :
    Nat.sub (Nat.shiftLeft (repU d d) d) (Nat.mul 2 (repU (d + 1) d)) =
      pk d (fun i => 2 ^ d - 2 ^ (i + 1)) d := by
  rcases Nat.eq_zero_or_pos d with h0 | hd
  · subst h0
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    rfl
  have e1 : Nat.shiftLeft (repU d d) d = pk d (fun _ => 2 ^ d) d := by
    change repU d d <<< d = _
    rw [Nat.shiftLeft_eq, repU_eq hd, Nat.mul_comm, pk_mul]
    simp
  have e2 : Nat.mul 2 (repU (d + 1) d) = pk d (fun i => 2 ^ (i + 1)) d := by
    change 2 * repU (d + 1) d = _
    rw [repU_eq (by omega), pk, pk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_mul, ← Nat.pow_succ', ← Nat.pow_add, Nat.succ_eq_add_one]
    congr 1
    ring
  change Nat.shiftLeft (repU d d) d - Nat.mul 2 (repU (d + 1) d) = _
  rw [e1, e2, pk, pk, pk, ← Finset.sum_tsub_distrib]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.sub_mul]
  · intro i hi
    have : i < d := Finset.mem_range.1 hi
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

private theorem pow_sub_bit {d a t : Nat} (ha : a ≤ d) :
    (2 ^ d - 2 ^ a).testBit t = (decide (a ≤ t) && decide (t < d)) := by
  have e : 2 ^ d - 2 ^ a = (2 ^ (d - a) - 1) <<< a := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← Nat.pow_add, Nat.sub_add_cancel ha]
  rw [e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
  omega

private theorem canonP_row {d : Nat} (hd : 2 ≤ d) (C i : Nat) (hi : i < d) :
    rowF d (canonP d C) i =
      (((rowF d C i ^^^ colB d C i) >>> (i + 1)) <<< (i + 1)) ||| (rowF d C i &&& (1 <<< i)) := by
  have hd0 : 0 < d := by omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [rowF_bit]
  unfold canonP diagP
  rw [strictN_eq', strictN_eq', su_eq]
  change (decide (j < d) && ((((C ^^^ trP d C) &&& pk d (fun i => 2 ^ d - 2 ^ (i + 1)) d) |||
    (C &&& repU (d + 1) d)).testBit (i * d + j))) = _
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, one_bit]
  by_cases hj : j < d
  · have hdiv : (i * d + j) / d = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd0, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (i * d + j) % d = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have hC : C.testBit (i * d + j) = (rowF d C i).testBit j := by rw [rowF_bit]; simp [hj]
    have hT : (trP d C).testBit (i * d + j) = (colB d C i).testBit j := by
      rw [← trP_row hd C i hi, rowF_bit]
      simp [hj]
    rw [hC, hT, pk_bit (u := fun i => 2 ^ d - 2 ^ (i + 1)) hd0
      (fun i => Nat.sub_lt (Nat.two_pow_pos d) (Nat.two_pow_pos _)), hdiv,
      hmod, pow_sub_bit (by omega), diag_bit hi hj]
    by_cases hij : i + 1 ≤ j
    · rw [show i + 1 + (j - (i + 1)) = j by omega]
      have hne : j ≠ i := by omega
      have hne' : j - i ≠ 0 := by omega
      simp [hj, hi, hij, hne, hne']
    · by_cases he : j = i
      · subst he
        simp [hj]
      · have h1 : ¬ i ≤ j := by omega
        simp [hj, hij, he, h1]
  · simp only [hj, decide_false, Bool.false_and]
    have hC : (rowF d C i).testBit j = false := by rw [rowF_bit]; simp [hj]
    have hT : (colB d C i).testBit j = false := by
      cases h : (colB d C i).testBit j
      · rfl
      · exact absurd ((colB_bit d C i j).1 h).1 hj
    rw [hC, Bool.false_and, Bool.or_false]
    cases hb : decide (j ≥ i + 1)
    · rfl
    · simp only [Bool.true_and]
      rw [show i + 1 + (j - (i + 1)) = j by simp at hb; omega, hC, hT]
      rfl

private theorem canonP_unpack {d : Nat} (hd : 2 ≤ d) (C : Nat) :
    canonRows d (unpackP d C) = unpackP d (canonP d C) := by
  apply Array.ext (by simp [canonRows, unpackP])
  intro i h1 h2
  have hi : i < d := by simpa [unpackP] using h2
  simp only [canonRows, Array.getElem_ofFn]
  rw [unpackP_get d C i hi]
  have hT : (transposeRows d (unpackP d C))[i]?.getD 0 = colB d C i := by
    rw [trP_unpack hd, unpackP_get d _ i hi, trP_row hd C i hi]
  rw [hT]
  simp only [unpackP, Array.getElem_ofFn]
  rw [canonP_row hd C i hi]

theorem pullK_sound {d A AT z z' : Nat} (hd : 2 ≤ d) (hT : Nat.beq (trP d A) AT = true)
    (h : pullK d A AT z z' = true) : pullOKZ d (unpackP d A) z z' = true := by
  unfold pullOKZ
  rw [triRows_eq, triRows_eq, trP_unpack hd, mulP_unpack (by omega), mulP_unpack (by omega),
    canonP_unpack hd, Nat.eq_of_beq_eq_true hT]
  unfold pullK at h
  rw [Nat.eq_of_beq_eq_true h]
  exact beq_self_eq_true _

theorem pullK_one_counterexample :
    pullK 1 1 (trP 1 1) 0 1 = true ∧ pullOKZ 1 (unpackP 1 1) 0 1 = false := by
  decide +kernel

private theorem getNK_eq : ∀ (L : List Nat) (i : Nat), getNK L i = L[i]?.getD 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => by
    change getNK L i = _
    rw [getNK_eq L i]
    rfl

private theorem lenNK_eq : ∀ L : List Nat, lenNK L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenNK L) = _
    rw [lenNK_eq L]
    rfl

private theorem tsK_spec {d : Nat} : ∀ (Ts TTs : List Nat), tsK d Ts TTs = true →
    ∀ i < Ts.length, getNK TTs i = trP d (getNK Ts i)
  | [], _, _, i, hi => absurd hi (by simp)
  | _ :: _, [], h, _, _ => absurd h Bool.false_ne_true
  | t :: ts, u :: us, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (tsK d ts us) (Nat.beq (trP d t) u) = true at h
    obtain ⟨h1, h2⟩ := bAnd_hx h
    cases i with
    | zero => exact (Nat.eq_of_beq_eq_true h1).symm
    | succ i => exact tsK_spec ts us h2 i (by simpa using hi)

private theorem vecMulN_congr {d : Nat} {R R' : Array Nat} (h : ∀ j < d, R[j]?.getD 0 = R'[j]?.getD 0)
    (v : Nat) : vecMulN d R v = vecMulN d R' v := by
  unfold vecMulN
  apply List.foldl_ext
  intro acc j hj
  rw [h j (List.mem_range.1 hj)]

private theorem mats_mul {d : Nat} (Ts : List Nat) (M : Array Nat) (x : Nat) :
    mulRows d M (Ts.toArray.map (unpackP d))[x]! = mulRows d M (unpackP d (getNK Ts x)) := by
  unfold mulRows
  congr 1
  funext r
  apply vecMulN_congr
  intro j hj
  rw [unpackP_get d _ j hj, getNK_eq]
  by_cases hx : x < Ts.length
  · rw [getElem!_pos _ x (by simpa using hx), Array.getElem_map, List.getElem_toArray,
      List.getElem?_eq_getElem hx, Option.getD_some, unpackP_get d _ j hj]
  · rw [getElem!_neg _ x (by simpa using hx), List.getElem?_eq_none (by omega), Option.getD_none]
    have h0 : rowF d 0 j = 0 := by
      apply Nat.eq_of_testBit_eq
      intro t
      rw [rowF_bit]
      simp
    rw [h0]
    rfl

private theorem mats_get {d : Nat} {Ts : List Nat} {x : Nat} (hx : x < Ts.length) :
    (Ts.toArray.map (unpackP d))[x]! = unpackP d (getNK Ts x) := by
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_map, List.getElem_toArray, getNK_eq,
    List.getElem?_eq_getElem hx, Option.getD_some]

private theorem prodK_run {d : Nat} (Ts : List Nat) : ∀ (ws : List Nat) (acc : Nat),
    unpackP d (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun x _ ih acc => strictN (mulF d acc (getNK Ts x)) fun acc' => ih acc') ws acc) =
      ws.foldl (fun M x => mulRows d M (Ts.toArray.map (unpackP d))[x]!) (unpackP d acc)
  | [], _ => rfl
  | x :: ws, acc => by
    change unpackP d (strictN (mulF d acc (getNK Ts x)) _) = _
    rw [strictN_eq', prodK_run Ts ws, List.foldl_cons, mats_mul, mulRows_unpack]

private theorem addRows_unpack (d X Y : Nat) :
    addRows (unpackP d X) (unpackP d Y) = unpackP d (Nat.xor X Y) := by
  apply Array.ext (by simp [addRows, unpackP])
  intro i h1 h2
  have hi : i < d := by simpa [unpackP] using h2
  simp only [addRows, Array.getElem_zipWith, unpackP, Array.getElem_ofFn]
  rw [rowF_xor]

private theorem combK_run {d : Nat} (Ts : List Nat) : ∀ (terms : List (List Nat)) (acc : Nat),
    terms.foldl (fun acc w => addRows acc (prodRows d (Ts.toArray.map (unpackP d)) w))
      (unpackP d acc) = unpackP d (Nat.xor acc (combK d Ts terms))
  | [], acc => by
    change unpackP d acc = unpackP d (Nat.xor acc 0)
    rw [show Nat.xor acc 0 = acc from Nat.xor_zero acc]
  | t :: ts, acc => by
    rw [List.foldl_cons]
    have e : prodRows d (Ts.toArray.map (unpackP d)) t = unpackP d (prodK d Ts t) := by
      unfold prodRows prodK
      rw [prodK_run, idF_unpack]
    rw [e, addRows_unpack, combK_run Ts ts]
    change unpackP d (Nat.xor (Nat.xor acc (prodK d Ts t)) (combK d Ts ts)) =
      unpackP d (Nat.xor acc (Nat.xor (prodK d Ts t) (combK d Ts ts)))
    rw [show ∀ a b c : Nat, Nat.xor (Nat.xor a b) c = Nat.xor a (Nat.xor b c) from
      fun a b c => Nat.xor_assoc a b c]

private theorem combRows_eq {d : Nat} (Ts : List Nat) (terms : List (List Nat)) :
    combRows d (Ts.toArray.map (unpackP d)) terms = unpackP d (combK d Ts terms) := by
  unfold combRows
  have e : zeroRows d = unpackP d 0 := by
    apply Array.ext (by simp [zeroRows, unpackP])
    intro i h1 h2
    simp only [zeroRows, Array.getElem_replicate, unpackP, Array.getElem_ofFn]
    apply Nat.eq_of_testBit_eq
    intro t
    rw [rowF_bit]
    simp
  rw [e, combK_run, show Nat.xor 0 (combK d Ts terms) = combK d Ts terms from Nat.zero_xor _]

private theorem projK_unpack {d v k : Nat} (hk : k < d) : projRows d v k = unpackP d (projK d v k) := by
  have hf : ∀ i < d, Nat.xor (pw2 i) (Bool.rec (motive := fun _ => Nat) 0 (pw2 k) (bit v i)) <
      2 ^ d := by
    intro i hi
    apply Nat.xor_lt_two_pow
    · rw [pw2_eq]
      exact Nat.pow_lt_pow_right (by norm_num) hi
    · cases bit v i
      · exact Nat.two_pow_pos d
      · rw [pw2_eq]
        exact Nat.pow_lt_pow_right (by norm_num) hk
  apply Array.ext (by simp [projRows, unpackP])
  intro i h1 h2
  have hi : i < d := by simpa [unpackP] using h2
  simp only [projRows, unpackP, Array.getElem_ofFn]
  rw [rowF, projK, fget_orN d d _ hf i hi, bit_eq]
  cases v.testBit i <;> rfl

private theorem mulVecRows_unpack {d : Nat} (hd : 2 ≤ d) (M v : Nat) :
    mulVecRows d (unpackP d M) v = vmF d (trP d M) v := by
  unfold mulVecRows
  rw [trP_unpack hd, vecMulN_eq]

private theorem spinK_spec {d nm : Nat} {TTs : List Nat} {PS : Nat} :
    ∀ (tree : List (Nat × Nat)) (i : Nat), spinK d nm TTs PS tree i = true →
      i + tree.length + 1 = d ∧ ∀ t (ht : t < tree.length), tree[t].1 ≤ i + t ∧
        tree[t].2 < nm ∧
        rowF d PS (i + t + 1) = vmF d (getNK TTs tree[t].2) (rowF d PS tree[t].1)
  | [], i, h => ⟨by have := Nat.eq_of_beq_eq_true h; simp; omega, fun t ht => absurd ht (by simp)⟩
  | (p, r) :: tr, i, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (spinK d nm TTs PS tr (Nat.succ i))
        (Nat.beq (rowF d PS (Nat.succ i)) (mvK d (getNK TTs r) (rowF d PS p))))
      (Nat.blt r nm)) (Nat.ble p i) = true at h
    obtain ⟨h1, h⟩ := bAnd_hx h
    obtain ⟨h2, h⟩ := bAnd_hx h
    obtain ⟨h3, h4⟩ := bAnd_hx h
    obtain ⟨a, b⟩ := spinK_spec tr (i + 1) h4
    refine ⟨by simp; omega, fun t ht => ?_⟩
    cases t with
    | zero =>
      exact ⟨by simpa using Nat.le_of_ble_eq_true h1, by simpa using Nat.blt_eq.mp h2,
        by simp only [List.getElem_cons_zero, Nat.add_zero]; exact Nat.eq_of_beq_eq_true h3⟩
    | succ t =>
      obtain ⟨c, e, f⟩ := b t (by simpa using ht)
      refine ⟨by simp; omega, by simpa using e, ?_⟩
      simp only [List.getElem_cons_succ]
      rw [show i + (t + 1) + 1 = i + 1 + t + 1 by omega]
      exact f

private theorem spin_foldl {d nm : Nat} (hd : 2 ≤ d) {Ts TTs : List Nat} {PS : Nat}
    (hlen : Ts.length = nm) (hts : ∀ i < Ts.length, getNK TTs i = trP d (getNK Ts i)) :
    ∀ (tree : List (Nat × Nat)) (i : Nat) (S : Array Nat), spinK d nm TTs PS tree i = true →
      S.size = i + 1 → (∀ j ≤ i, S[j]! = rowF d PS j) →
      tree.foldl (fun S t => S.push (mulVecRows d (Ts.toArray.map (unpackP d))[t.2]! S[t.1]!)) S =
        unpackP d PS
  | [], i, S, h, hS, hj => by
    change S = unpackP d PS
    have hi : i + 1 = d := Nat.eq_of_beq_eq_true h
    apply Array.ext (by simp [unpackP]; omega)
    intro j h1 h2
    have hjd : j < d := by simpa [unpackP] using h2
    rw [← getElem!_pos S j h1, hj j (by omega)]
    simp [unpackP]
  | (p, r) :: tr, i, S, h, hS, hj => by
    obtain ⟨-, hsp⟩ := spinK_spec ((p, r) :: tr) i h
    obtain ⟨hp, hr, he⟩ := hsp 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hp hr he
    have h' : spinK d nm TTs PS tr (i + 1) = true := by
      change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (spinK d nm TTs PS tr (Nat.succ i))
          (Nat.beq (rowF d PS (Nat.succ i)) (mvK d (getNK TTs r) (rowF d PS p))))
        (Nat.blt r nm)) (Nat.ble p i) = true at h
      exact (bAnd_hx (bAnd_hx (bAnd_hx h).2).2).2
    rw [List.foldl_cons]
    refine spin_foldl hd hlen hts tr (i + 1) _ h' (by simp [hS]) (fun j hj' => ?_)
    have hpush : (mulVecRows d (Ts.toArray.map (unpackP d))[r]! S[p]!) = rowF d PS (i + 1) := by
      rw [mats_get (by omega), hj p hp, mulVecRows_unpack hd, he, hts r (by omega)]
    rcases Nat.lt_or_ge j (i + 1) with hlt | hge
    · rw [getElem!_pos _ j (by simp; omega), Array.getElem_push_lt (by omega),
        ← getElem!_pos S j (by omega)]
      exact hj j (by omega)
    · have hjs : j = S.size := by omega
      rw [hjs, getElem!_pos _ _ (by simp), Array.getElem_push_eq, hpush]
      rw [hS]

theorem sepK_sound {d nm : Nat} {Ts TTs : List Nat} {terms : List (List Nat)}
    {v k K KT PP PS PX : Nat} {tree : List (Nat × Nat)} (hd : 2 ≤ d)
    (h : sepK d nm Ts TTs terms v k K KT PP PS PX tree = true) :
    CFSG.Sporadic.Schreier.PairF2.sepF2OK d (Ts.toArray.map (unpackP d)) terms v k (unpackP d PP)
      (unpackP d PX) tree (unpackP d PS) = true ∧
      CFSG.Sporadic.Schreier.PairF2.spinVecs d (Ts.toArray.map (unpackP d)) v tree =
        unpackP d PS := by
  unfold sepK at h
  obtain ⟨hlen, h⟩ := bAnd_hx h
  obtain ⟨hts, h⟩ := bAnd_hx h
  obtain ⟨hk, h⟩ := bAnd_hx h
  obtain ⟨hvk, h⟩ := bAnd_hx h
  obtain ⟨hK, h⟩ := bAnd_hx h
  obtain ⟨hKT, h⟩ := bAnd_hx h
  obtain ⟨hmv, h⟩ := bAnd_hx h
  obtain ⟨hP, h⟩ := bAnd_hx h
  obtain ⟨hS0, h⟩ := bAnd_hx h
  obtain ⟨hsp, hX⟩ := bAnd_hx h
  have hlen : Ts.length = nm := by rw [← lenNK_eq]; exact Nat.eq_of_beq_eq_true hlen
  have hts := tsK_spec Ts TTs hts
  have hk : k < d := Nat.blt_eq.mp hk
  have hK : K = combK d Ts terms := Nat.eq_of_beq_eq_true hK
  have hKT : trP d K = KT := Nat.eq_of_beq_eq_true hKT
  have hS0 : rowF d PS 0 = v := Nat.eq_of_beq_eq_true hS0
  obtain ⟨htl, hspin⟩ := spinK_spec tree 0 hsp
  have hcomb := combRows_eq (d := d) Ts terms
  rw [← hK] at hcomb
  have hspv : spinVecs d (Ts.toArray.map (unpackP d)) v tree = unpackP d PS := by
    unfold spinVecs
    refine spin_foldl hd hlen hts tree 0 #[v] hsp (by simp) (fun j hj => ?_)
    have : j = 0 := by omega
    subst this
    simp [hS0]
  refine ⟨?_, hspv⟩
  unfold sepF2OK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [← bit_eq]
    exact hvk
  · rw [Array.all_eq_true]
    intro i hi
    simp [unpackP]
  · rw [hcomb, mulVecRows_unpack hd, hKT]
    exact Nat.eq_of_beq_eq_true hmv
  · simp [unpackP]
  · rw [hcomb, mulRows_unpack, Nat.eq_of_beq_eq_true hP, projK_unpack hk]
  · simp [unpackP]
    omega
  · rw [getElem!_pos _ 0 (by simp [unpackP]; omega)]
    simp [unpackP, hS0]
  · rw [List.all_eq_true]
    intro i hi'
    have hi : i < tree.length := List.mem_range.1 hi'
    obtain ⟨hp, hr, hv⟩ := hspin i hi
    rw [Nat.zero_add] at hp hv
    have hp' : tree[i].1 < d := by omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [getElem!_pos tree i hi]
    refine ⟨⟨hp, by simp [hlen, hr]⟩, ?_⟩
    rw [mats_get (by omega), getElem!_pos _ (i + 1) (by simp [unpackP]; omega),
      getElem!_pos _ tree[i].1 (by simp [unpackP]; omega)]
    have e1 : (unpackP d PS)[i + 1]'(by simp [unpackP]; omega) = rowF d PS (i + 1) := by
      simp [unpackP]
    have e2 : (unpackP d PS)[tree[i].1]'(by simp [unpackP]; omega) = rowF d PS tree[i].1 := by
      simp [unpackP]
    rw [e1, e2, mulVecRows_unpack hd, ← hts _ (by omega), hv]
  · simp [unpackP]
  · simp [unpackP]
  · exact mulF_id_sound hX

theorem sepK_one_counterexample :
    sepK 1 1 [1] [trP 1 1] [[0]] 1 0 1 (trP 1 1) 0 1 1 [] = true ∧
      combK 1 [1] [[0]] = 1 ∧ mulVecRows 1 (unpackP 1 1) 1 = 1 := by
  decide +kernel

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem formB_sound {d w m A1 A1T A2 A2T P0 P1 : Nat} {F : Nat → Nat} {r : Nat} (hd : 2 ≤ d)
    (hT1 : Nat.beq (trP d A1) A1T = true) (hT2 : Nat.beq (trP d A2) A2T = true)
    (h : formB d w m A1 A1T A2 A2T P0 P1 F r = true) :
    packRowsZ d (triRowsZ d (F r)) = F r ∧
      pullOKZ d (unpackP d A1) (F r) (F (CFSG.KC.Enum.pg w m P0 r)) = true ∧
      pullOKZ d (unpackP d A2) (F r) (F (CFSG.KC.Enum.pg w m P1 r)) = true := by
  unfold formB at h
  rw [strictB_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨packK_sound h.1, pullK_sound hd hT1 h.2.1, pullK_sound hd hT2 h.2.2⟩

end CFSG.KS.SporSch.PF2

end
