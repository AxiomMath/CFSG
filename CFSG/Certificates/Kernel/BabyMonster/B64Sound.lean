module

public import CFSG.Certificates.Kernel.BabyMonster.B64
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerArith
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.BM.B64

@[expose] noncomputable def ascC (N len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (Nat.blt (chAt N i) (nat_lit 128)) ih) len

@[expose] noncomputable def asciiOK (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun N len => ascC N len) p) ih) L

theorem asciiOK_neg : asciiOK [(65 + 256 * 200, 2)] = false := by decide +kernel

theorem asciiOK_append : ∀ {L₁ L₂ : List (Nat × Nat)}, asciiOK L₁ = true → asciiOK L₂ = true →
    asciiOK (L₁ ++ L₂) = true
  | [], _, _, h₂ => h₂
  | (N, len) :: L₁, L₂, h₁, h₂ => by
    change andB (ascC N len) (asciiOK L₁) = true at h₁
    change andB (ascC N len) (asciiOK (L₁ ++ L₂)) = true
    cases hc : ascC N len
    · rw [hc] at h₁
      exact h₁
    · rw [hc] at h₁
      exact asciiOK_append h₁ h₂

end CFSG.KC.BM.B64

end

namespace CFSG.KC.BM.B64

open CFSG.KC.YModel CFSG.Monster.B.Bin

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem chAt_zero (N : Nat) : chAt N 0 = N &&& 255 := by
  unfold chAt
  change (N >>> (8 * 0)) &&& 255 = _
  simp

theorem chAt_succ (N i : Nat) : chAt N (i + 1) = chAt (N >>> 8) i := by
  unfold chAt
  change (N >>> (8 * (i + 1))) &&& 255 = ((N >>> 8) >>> (8 * i)) &&& 255
  rw [← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]

theorem chAt_lt (N i : Nat) : chAt N i < 256 := by
  unfold chAt
  exact Nat.lt_succ_of_le (Nat.and_le_right)

theorem decChunk_succ (len N : Nat) (t : List Nat) :
    decChunk (len + 1) N t = (N &&& 255) :: decChunk len (N >>> 8) t := rfl

theorem decChunk_get_lt : ∀ (len N : Nat) (t : List Nat) (i : Nat), i < len →
    (decChunk len N t)[i]? = some (chAt N i)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | len + 1, N, t, 0, _ => by rw [decChunk_succ, chAt_zero]; rfl
  | len + 1, N, t, i + 1, h => by
    rw [decChunk_succ, List.getElem?_cons_succ, chAt_succ]
    exact decChunk_get_lt len _ t i (by omega)

theorem decChunk_get_ge : ∀ (len N : Nat) (t : List Nat) (i : Nat),
    (decChunk len N t)[len + i]? = t[i]?
  | 0, _, _, i => by rw [Nat.zero_add]; rfl
  | len + 1, N, t, i => by
    rw [decChunk_succ, Nat.add_right_comm, List.getElem?_cons_succ]
    exact decChunk_get_ge len _ t i

theorem decChunk_mem : ∀ (len N : Nat) (t : List Nat) (x : Nat), x ∈ decChunk len N t →
    (∃ i < len, x = chAt N i) ∨ x ∈ t
  | 0, _, _, _, h => Or.inr h
  | len + 1, N, t, x, h => by
    rw [decChunk_succ, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl ⟨0, by omega, by rw [chAt_zero]; exact h⟩
    · rcases decChunk_mem len _ t x h with ⟨i, hi, rfl⟩ | h
      · exact Or.inl ⟨i + 1, by omega, (chAt_succ N i).symm⟩
      · exact Or.inr h

theorem decChunkC_eq : ∀ (len N : Nat) (t : List Nat),
    decChunkC len N (t.map Char.ofNat) = (decChunk len N t).map Char.ofNat
  | 0, _, _ => rfl
  | len + 1, N, t => by
    rw [decChunk_succ, List.map_cons, ← decChunkC_eq len (N >>> 8) t]
    rfl

theorem charsOf_eq : ∀ L : List (Nat × Nat), charsOf L = (bytesOf L).map Char.ofNat
  | [] => rfl
  | (N, len) :: L => by
    change decChunkC len N (charsOf L) = (decChunk len N (bytesOf L)).map Char.ofNat
    rw [charsOf_eq L, decChunkC_eq]

theorem bytesOf_cons (N len : Nat) (L : List (Nat × Nat)) :
    bytesOf ((N, len) :: L) = decChunk len N (bytesOf L) := rfl

theorem ascC_spec : ∀ (N len : Nat), ascC N len = true → ∀ i < len, chAt N i < 128
  | _, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | N, len + 1, h, i, hi => by
    change andB (Nat.blt (chAt N len) 128) (ascC N len) = true at h
    rw [andB_eq_true, Nat.blt_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ascC_spec N len h.2 i hi
    · exact h.1

theorem bytesOf_lt : ∀ L : List (Nat × Nat), asciiOK L = true → ∀ x ∈ bytesOf L, x < 128
  | [], _, _, h => absurd h List.not_mem_nil
  | (N, len) :: L, h, x, hx => by
    change andB (ascC N len) (asciiOK L) = true at h
    rw [andB_eq_true] at h
    rw [bytesOf_cons] at hx
    rcases decChunk_mem len N _ x hx with ⟨i, hi, rfl⟩ | hx
    · exact ascC_spec N len h.1 i hi
    · exact bytesOf_lt L h.2 x hx

theorem utf8_ascii : ∀ l : List Nat, (∀ x ∈ l, x < 128) →
    (l.map Char.ofNat).flatMap String.utf8EncodeChar = l.map UInt8.ofNat
  | [], _ => rfl
  | x :: l, h => by
    have hx : x < 128 := h x List.mem_cons_self
    rw [List.map_cons, List.flatMap_cons, List.map_cons,
      utf8_ascii l (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hv : (Char.ofNat x).val.toNat = x := by
      rw [Char.ofNat, dite_eq_left (by left; omega)]
      simp [Char.ofNatAux]
    simp [String.utf8EncodeChar, hv, Nat.le_of_lt_succ hx]

theorem toUTF8_ascii (l : List Nat) (h : ∀ x ∈ l, x < 128) :
    (String.ofList (l.map Char.ofNat)).toUTF8.data.toList = l.map UInt8.ofNat := by
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode,
    List.toList_data_toByteArray, utf8_ascii l h]

theorem get!_eq (b : ByteArray) (i : Nat) : b.get! i = b.data.toList[i]! := by
  rcases b with ⟨xs⟩
  simp only [ByteArray.get!, Array.getElem!_toList]

theorem size_eq (b : ByteArray) : b.size = b.data.toList.length := by
  rcases b with ⟨xs⟩
  simp [ByteArray.size]

def Dq (b : ByteArray) (q : Nat) : Nat :=
  (b64Val (b.get! (4 * q)) <<< 18) ||| (b64Val (b.get! (4 * q + 1)) <<< 12) |||
    (b64Val (b.get! (4 * q + 2)) <<< 6) ||| b64Val (b.get! (4 * q + 3))

def Db (b : ByteArray) (p : Nat) : UInt8 := UInt8.ofNat (Dq b (p / 3) >>> (16 - 8 * (p % 3)))

theorem quad_spec (b : ByteArray) (len m : Nat) (out : ByteArray)
    (ho : out.data.toList = (List.range (3 * m)).map (Db b)) (hm : 3 * m < len) :
    (b64Quad b len (4 * m) out).data.toList = (List.range (min len (3 * m + 3))).map (Db b) := by
  have hs : out.size = 3 * m := by rw [size_eq, ho, List.length_map, List.length_range]
  have e0 : Db b (3 * m) = UInt8.ofNat (Dq b m >>> 16) := by
    have d : 3 * m / 3 = m := by omega
    have r : 3 * m % 3 = 0 := by omega
    simp only [Db]
    rw [d, r]
  have e1 : Db b (3 * m + 1) = UInt8.ofNat (Dq b m >>> 8) := by
    have d : (3 * m + 1) / 3 = m := by omega
    have r : (3 * m + 1) % 3 = 1 := by omega
    simp only [Db]
    rw [d, r]
  have e2 : Db b (3 * m + 2) = UInt8.ofNat (Dq b m) := by
    have d : (3 * m + 2) / 3 = m := by omega
    have r : (3 * m + 2) % 3 = 2 := by omega
    simp only [Db]
    rw [d, r]
    simp
  have r1 : List.range (3 * m + 1) = List.range (3 * m) ++ [3 * m] := List.range_succ
  have r2 : List.range (3 * m + 2) = List.range (3 * m + 1) ++ [3 * m + 1] := List.range_succ
  have r3 : List.range (3 * m + 3) = List.range (3 * m + 2) ++ [3 * m + 2] := List.range_succ
  unfold b64Quad
  by_cases h1 : 3 * m + 1 < len
  · by_cases h2 : 3 * m + 2 < len
    · rw [Nat.min_eq_right (by omega), r3, r2, r1]
      simp [ByteArray.size_push, hs, hm, h1, h2, ho, e0, e1, e2, Dq]
    · have hl : len = 3 * m + 2 := by omega
      rw [Nat.min_eq_left (by omega), hl, r2, r1]
      simp [ByteArray.size_push, hs, ho, e0, e1, Dq]
  · have hl : len = 3 * m + 1 := by omega
    rw [Nat.min_eq_left (by omega), hl, r1]
    simp [ByteArray.size_push, hs, ho, e0, Dq]

theorem go_done (b : ByteArray) (len : Nat) : ∀ (fuel i : Nat) (out : ByteArray), len ≤ out.size →
    b64Go b len fuel i out = out
  | 0, _, _, _ => rfl
  | fuel + 1, i, out, h => by
    rw [b64Go, ite_eq_right (by omega)]

theorem go_spec (b : ByteArray) (len : Nat) : ∀ (fuel m : Nat) (out : ByteArray),
    out.data.toList = (List.range (3 * m)).map (Db b) → 3 * m ≤ len → len ≤ 3 * m + 3 * fuel →
    (b64Go b len fuel (4 * m) out).data.toList = (List.range len).map (Db b)
  | 0, m, out, ho, h1, h2 => by
    have hl : len = 3 * m := by omega
    rw [hl]
    exact ho
  | fuel + 1, m, out, ho, h1, h2 => by
    have hs : out.size = 3 * m := by rw [size_eq, ho, List.length_map, List.length_range]
    by_cases hm : 3 * m < len
    · rw [b64Go, ite_eq_left (by omega)]
      have hq := quad_spec b len m out ho hm
      by_cases h3 : 3 * m + 3 ≤ len
      · rw [Nat.min_eq_right h3] at hq
        have e : 4 * m + 4 = 4 * (m + 1) := by omega
        rw [e]
        exact go_spec b len fuel (m + 1) _ hq (by omega) (by omega)
      · rw [Nat.min_eq_left (by omega)] at hq
        have hl : len ≤ (b64Quad b len (4 * m) out).size := by
          rw [size_eq, hq, List.length_map, List.length_range]
          exact Nat.le_refl _
        rw [go_done b len fuel _ _ hl]
        exact hq
    · have hl : len = 3 * m := by omega
      rw [go_done b _ _ _ _ (by omega), hl]
      exact ho

theorem decode_get (s : String) (len P : Nat) (hP : P < len) :
    (b64Decode s len).get! P = Db s.toUTF8 P := by
  have h0 : (ByteArray.emptyWithCapacity len).data.toList = (List.range (3 * 0)).map
      (Db s.toUTF8) := rfl
  have h := go_spec s.toUTF8 len (len / 3 + 1) 0 _ h0 (by omega) (by omega)
  rw [Nat.mul_zero] at h
  rw [b64Decode, get!_eq, h, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hP]
  rfl

theorem b64Val_ofNat : ∀ x < 256, b64Val (UInt8.ofNat x) = b64v x := by decide +kernel

theorem b64v_lt : ∀ x < 256, b64v x < 64 := by decide +kernel

theorem toNat_ofNat8 (x : Nat) : (UInt8.ofNat x).toNat = x % 256 := by
  simp

theorem b64Val_lt (c : UInt8) : b64Val c < 64 := by
  unfold b64Val
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · omega
  split <;> omega

def quad4 (a b c d : Nat) : Nat := (a <<< 18) ||| (b <<< 12) ||| (c <<< 6) ||| d

theorem testBit_lt64 {c : Nat} (hc : c < 64) {n : Nat} (hn : 6 ≤ n) : c.testBit n = false := by
  have h : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  exact Nat.testBit_lt_two_pow (by omega)

theorem quad4_hi {a b c d c' d' : Nat} (hc : c < 64) (hd : d < 64) (hc' : c' < 64) (hd' : d' < 64)
    (i : Nat) : (quad4 a b c d).testBit (16 + i) = (quad4 a b c' d').testBit (16 + i) := by
  simp only [quad4, Nat.testBit_or, Nat.testBit_shiftLeft]
  rw [testBit_lt64 hc (by omega), testBit_lt64 hd (by omega), testBit_lt64 hc' (by omega),
    testBit_lt64 hd' (by omega)]

theorem quadV_eq (N k : Nat) : quadV N k = quad4 (b64v (chAt N (4 * k))) (b64v (chAt N (4 * k + 1)))
    (b64v (chAt N (4 * k + 2))) (b64v (chAt N (4 * k + 3))) := by
  unfold quadV quad4
  exact (Nat.or_assoc _ _ _).symm

theorem testBit_Db (b : ByteArray) (p i : Nat) (hi : i < 8) :
    (Db b p).toNat.testBit i = (Dq b (p / 3)).testBit (16 - 8 * (p % 3) + i) := by
  have e : (256 : Nat) = 2 ^ 8 := rfl
  rw [Db, toNat_ofNat8, e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hi]

theorem testBit_tripleOf (v x : Nat) : (tripleOf v).testBit x =
    (decide (x < 24) && v.testBit (16 - 8 * (x / 8) + x % 8)) := by
  unfold tripleOf
  change ((v >>> 16) &&& 255 ||| (((v >>> 8) &&& 255) <<< 8 ||| ((v &&& 255) <<< 16))).testBit x = _
  have e : (255 : Nat) = 2 ^ 8 - 1 := rfl
  rw [e]
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h0 : x < 8
  · have e1 : x / 8 = 0 := by omega
    have e2 : x % 8 = x := by omega
    have f1 : ¬ 8 ≤ x := by omega
    have f2 : ¬ 16 ≤ x := by omega
    have f3 : x < 24 := by omega
    simp [e1, e2, f1, f2, f3, h0]
  by_cases h1 : x < 16
  · have e1 : x / 8 = 1 := by omega
    have e2 : 16 - 8 * 1 + x % 8 = x := by omega
    have f1 : 8 ≤ x := by omega
    have f2 : ¬ 16 ≤ x := by omega
    have f3 : x < 24 := by omega
    have f4 : x - 8 < 8 := by omega
    have f5 : 8 + (x - 8) = x := by omega
    simp [e1, e2, f1, f2, f3, f4, f5, h0]
  by_cases h2 : x < 24
  · have e1 : x / 8 = 2 := by omega
    have e2 : 16 - 8 * 2 + x % 8 = x - 16 := by omega
    have f4 : x - 16 < 8 := by omega
    have f2 : 16 ≤ x := by omega
    have f5 : ¬ x - 8 < 8 := by omega
    simp [e1, e2, f2, f4, f5, h0, h2]
  have f4 : ¬ x - 16 < 8 := by omega
  have f5 : ¬ x - 8 < 8 := by omega
  have f6 : ¬ x < 8 := by omega
  simp [h2, f4, f5, f6]

theorem forceB_eq (v : Nat) (k : Nat → Nat) : forceB v k = k v := by
  unfold forceB
  cases Nat.beq v 0 <;> rfl

theorem segDec_succ (N q : Nat) :
    segDec N (q + 1) = segDec N q ||| (tripleOf (quadV N q) <<< (24 * q)) := by
  change forceB (segDec N q) (fun a => a ||| (tripleOf (quadV N q) <<< (24 * q))) = _
  rw [forceB_eq]

theorem testBit_segDec (N : Nat) : ∀ q x : Nat, (segDec N q).testBit x =
    (decide (x < 24 * q) && (tripleOf (quadV N (x / 24))).testBit (x % 24))
  | 0, x => by
    change (0 : Nat).testBit x = _
    simp
  | q + 1, x => by
    rw [segDec_succ, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_segDec N q x]
    by_cases h : x < 24 * q
    · have h' : x < 24 * (q + 1) := by omega
      have h'' : ¬ 24 * q ≤ x := by omega
      simp [h, h', h'']
    by_cases h2 : x < 24 * (q + 1)
    · have e1 : x / 24 = q := by omega
      have e2 : x % 24 = x - 24 * q := by omega
      have h'' : 24 * q ≤ x := by omega
      simp [h, h2, h'', e1, e2]
    · have h'' : 24 * q ≤ x := by omega
      have h3 : ¬ x - 24 * q < 24 := by omega
      simp [h, h2, h'', testBit_tripleOf, h3]

theorem testBit_segDec_byte (N q c i : Nat) (hc : c < 3 * q) (hi : i < 8) :
    (segDec N q).testBit (8 * c + i) = (quadV N (c / 3)).testBit (16 - 8 * (c % 3) + i) := by
  rw [testBit_segDec, testBit_tripleOf]
  have e1 : (8 * c + i) / 24 = c / 3 := by omega
  have e2 : (8 * c + i) % 24 / 8 = c % 3 := by omega
  have e3 : (8 * c + i) % 24 % 8 = i := by omega
  have f1 : 8 * c + i < 24 * q := by omega
  have f2 : (8 * c + i) % 24 < 24 := by omega
  simp [e1, e2, e3, f1, f2]

theorem testBit_lastByte (r i : Nat) :
    (lastByte r).testBit i = (decide (i < 8) && r.testBit (4408 + i)) := by
  unfold lastByte
  change ((r >>> 4408) &&& (2 ^ 8 - 1)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem testBit_mask (n i : Nat) : ((1 <<< n) - 1).testBit i = decide (i < n) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem testBit_low551 (i : Nat) : low551.testBit i = decide (i < 4408) :=
  testBit_mask 4408 i

theorem testBit_segWant_hi (R : Nat → Nat) (j c i : Nat) (hc : 1 ≤ c) (hi : i < 8) :
    (segWant R j).testBit (8 * c + i) =
      (decide (8 * (c - 1) + i < 4408) && (R j).testBit (8 * (c - 1) + i)) := by
  unfold segWant
  change (Nat.rec (motive := fun _ => Nat) 0 (fun i _ => lastByte (R i)) j |||
    ((R j &&& low551) <<< 8)).testBit (8 * c + i) = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, testBit_low551]
  have e : 8 * c + i - 8 = 8 * (c - 1) + i := by omega
  have f : 8 ≤ 8 * c + i := by omega
  have h0 : (Nat.rec (motive := fun _ => Nat) 0 (fun i _ => lastByte (R i)) j : Nat).testBit
      (8 * c + i) = false := by
    cases j with
    | zero => exact Nat.zero_testBit _
    | succ j =>
      change (lastByte (R j)).testBit _ = false
      rw [testBit_lastByte]
      have : ¬ 8 * c + i < 8 := by omega
      simp [this]
  rw [h0, e]
  simp [f, Bool.and_comm]

theorem testBit_segWant_lo (R : Nat → Nat) (j i : Nat) (hi : i < 8) :
    (segWant R (j + 1)).testBit i = (R j).testBit (4408 + i) := by
  unfold segWant
  change (lastByte (R j) ||| ((R (j + 1) &&& low551) <<< 8)).testBit i = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_lastByte]
  have : ¬ 8 ≤ i := by omega
  simp [this, hi]

theorem lenP_eq : ∀ L : List (Nat × Nat), lenP L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenP_eq L)

theorem dropP_eq : ∀ (L : List (Nat × Nat)) (k : Nat), dropP L k = L.drop k
  | [], k => by cases k <;> rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => dropP_eq L k

theorem getP_eq (L : List (Nat × Nat)) (k : Nat) : getP L k = (L[k]?).getD (0, 0) := by
  unfold getP
  rw [dropP_eq, ← List.head?_drop]
  cases L.drop k <;> rfl

theorem rangeOK_spec (R : Nat → Nat) : ∀ (L : List (Nat × Nat)) (j c : Nat),
    rangeOK L j c R = true → ∀ i < c, ∃ p, L[i]? = some p ∧ segOK R (j + i) p = true
  | [], j, c, h, i, hi => by
    change Nat.beq c 0 = true at h
    have := Nat.eq_of_beq_eq_true h
    omega
  | p :: L, j, c, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) (andB (segOK R j p) (rangeOK L (j + 1) (c - 1) R))
      true (Nat.beq c 0) = true at h
    cases hc : Nat.beq c 0 with
    | true =>
      have := Nat.eq_of_beq_eq_true hc
      omega
    | false => ?_
    rw [hc, andB_eq_true] at h
    cases i with
    | zero => exact ⟨p, rfl, h.1⟩
    | succ i =>
      obtain ⟨q, hq, hs⟩ := rangeOK_spec R L (j + 1) (c - 1) h.2 i (by omega)
      refine ⟨q, hq, ?_⟩
      have e : j + (i + 1) = j + 1 + i := by omega
      rw [e]
      exact hs

theorem lt_rowsS (s i : Nat) (hi : i < 64) (h : 64 * s + i < 4370) : i < rowsS s := by
  unfold rowsS
  change i < Bool.rec (motive := fun _ => Nat) 64 (4370 - 64 * s) (Nat.ble (4370 - 64 * s) 64)
  cases hb : Nat.ble (4370 - 64 * s) 64
  · exact hi
  · change i < 4370 - 64 * s
    omega

theorem bytesOf_get : ∀ (L : List (Nat × Nat)) (j : Nat) (p : Nat × Nat), L[j]? = some p →
    (∀ j' q, j' < j → L[j']? = some q → q.2 = 736) →
    ∀ i < p.2, (bytesOf L)[736 * j + i]? = some (chAt p.1 i)
  | [], _, _, h, _, _, _ => by simp at h
  | (N, len) :: L, 0, p, h, _, i, hi => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [bytesOf_cons, Nat.mul_zero, Nat.zero_add]
    exact decChunk_get_lt len N _ i hi
  | (N, len) :: L, j + 1, p, h, hb, i, hi => by
    have h0 : len = 736 := hb 0 (N, len) (by omega) rfl
    have e : 736 * (j + 1) + i = len + (736 * j + i) := by omega
    rw [bytesOf_cons, e, decChunk_get_ge]
    exact bytesOf_get L j p h (fun j' q hj hq => hb (j' + 1) q (by omega) hq) i hi

theorem testBit_land255 (x i : Nat) (hi : i < 8) : (x &&& 255).testBit i = x.testBit i := by
  have e : (255 : Nat) = 2 ^ 8 - 1 := rfl
  rw [Nat.testBit_and, e, Nat.testBit_two_pow_sub_one]
  simp [hi]

end CFSG.KC.BM.B64

public section

namespace CFSG.KC.BM.B64

open CFSG.KC.YModel CFSG.Monster.B.Bin

theorem b64Decode_rows {CH : List (Nat × Nat)} {R : Nat → Nat}
    (hasc : asciiOK CH = true)
    (hlen : Nat.beq (lenP CH) (nat_lit 4372) = true)
    (hh : hdrOK (getP CH 0) = true)
    (hr : ∀ s < 69, rangeOK (dropP CH (1 + 64 * s)) (64 * s) (rowsS s) R = true)
    (hl : lastOK R (getP CH 4371) = true) :
    ∀ k t : Nat, k < 4370 → t < 4416 →
      ((CFSG.Monster.B.Bin.b64Decode (String.ofList (CFSG.KC.YModel.charsOf CH)) 2412256).get!
        (16 + 552 * k + t / 8)).toNat.testBit (t % 8) = (R k).testBit t := by
  intro k t hk ht
  have hlen' : CH.length = 4372 := by
    rw [← lenP_eq]
    exact Nat.eq_of_beq_eq_true hlen
  obtain ⟨N0, len0, L, rfl⟩ : ∃ N0 len0 L, CH = (N0, len0) :: L := by
    cases CH with
    | nil => simp at hlen'
    | cons p0 L => exact ⟨p0.1, p0.2, L, rfl⟩
  have hLlen : L.length = 4371 := by
    simp only [List.length_cons] at hlen'
    omega
  have h20 : len0 = 20 := by
    rw [getP_eq] at hh
    change andB (Nat.beq len0 20) _ = true at hh
    exact Nat.eq_of_beq_eq_true (andB_eq_true.1 hh).1
  have hseg : ∀ j p, j < 4370 → L[j]? = some p → p.2 = 736 ∧ segDec p.1 184 = segWant R j := by
    intro j p hj hp
    have hs : j / 64 < 69 := by omega
    obtain ⟨q, hq, hok⟩ := rangeOK_spec R _ _ _ (hr (j / 64) hs) (j % 64)
      (lt_rowsS _ _ (by omega) (by omega))
    have e1 : 1 + 64 * (j / 64) + j % 64 = j + 1 := by omega
    have e2 : 64 * (j / 64) + j % 64 = j := by omega
    rw [dropP_eq, List.getElem?_drop, e1, List.getElem?_cons_succ, hp, Option.some.injEq] at hq
    rw [e2, ← hq] at hok
    change andB (Nat.beq p.2 736) (Nat.beq (segDec p.1 184) (segWant R j)) = true at hok
    rw [andB_eq_true] at hok
    exact ⟨Nat.eq_of_beq_eq_true hok.1, Nat.eq_of_beq_eq_true hok.2⟩
  have hpre : ∀ j, j ≤ 4370 → ∀ j' q, j' < j → L[j']? = some q → q.2 = 736 :=
    fun j hj j' q hj' hq => (hseg j' q (by omega) hq).1
  obtain ⟨pl, hpl⟩ : ∃ pl, L[4370]? = some pl := ⟨L[4370], List.getElem?_eq_getElem (by omega)⟩
  rw [getP_eq, List.getElem?_cons_succ, hpl] at hl
  change andB (Nat.beq pl.2 2)
    (Nat.beq (segDec pl.1 1 &&& 255) (lastByte (R 4369))) = true at hl
  rw [andB_eq_true] at hl
  have hpl2 : pl.2 = 2 := Nat.eq_of_beq_eq_true hl.1
  have hpl1 : segDec pl.1 1 &&& 255 = lastByte (R 4369) := Nat.eq_of_beq_eq_true hl.2
  generalize hBdef : bytesOf ((N0, len0) :: L) = B
  have hB : ∀ x ∈ B, x < 128 := hBdef ▸ bytesOf_lt _ hasc
  generalize hsdef : String.ofList (charsOf ((N0, len0) :: L)) = s
  have hdata : s.toUTF8.data.toList = B.map UInt8.ofNat := by
    rw [← hsdef, charsOf_eq, hBdef]
    exact toUTF8_ascii _ hB
  have hG : ∀ y : Nat, (B[y]?).getD 0 < 256 := by
    intro y
    cases hy : B[y]? with
    | none => exact Nat.zero_lt_succ _
    | some x =>
      have := hB x (List.mem_of_getElem? hy)
      change x < 256
      omega
  have hval : ∀ y : Nat, b64Val (s.toUTF8.get! y) = b64v ((B[y]?).getD 0) := by
    intro y
    rw [← b64Val_ofNat _ (hG y), get!_eq, hdata, List.getElem!_eq_getElem?_getD, List.getElem?_map]
    cases B[y]? <;> rfl
  have hDq : ∀ q : Nat, Dq s.toUTF8 q =
      quad4 (b64v ((B[4 * q]?).getD 0)) (b64v ((B[4 * q + 1]?).getD 0))
        (b64v ((B[4 * q + 2]?).getD 0)) (b64v ((B[4 * q + 3]?).getD 0)) := by
    intro q
    unfold Dq quad4
    rw [hval, hval, hval, hval]
  have hGL : ∀ j p, j ≤ 4370 → L[j]? = some p → ∀ i < p.2,
      (B[20 + 736 * j + i]?).getD 0 = chAt p.1 i := by
    intro j p hj hp i hi
    rw [← hBdef, bytesOf_cons, ← h20, Nat.add_assoc, decChunk_get_ge,
      bytesOf_get L j p hp (hpre j hj) i hi]
    rfl
  have hbyte : ∀ P < 2412256, (b64Decode s 2412256).get! P = Db s.toUTF8 P :=
    fun P hP => decode_get s 2412256 P hP
  have hchunk : ∀ j < 4370, ∀ c < 552, ∀ i < 8,
      ((b64Decode s 2412256).get! (15 + 552 * j + c)).toNat.testBit i =
        (segWant R j).testBit (8 * c + i) := by
    intro j hj c hc i hi
    obtain ⟨p, hp⟩ : ∃ p, L[j]? = some p := ⟨L[j], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨h736, hsd⟩ := hseg j p hj hp
    have e1 : (15 + 552 * j + c) / 3 = 5 + 184 * j + c / 3 := by omega
    have e2 : (15 + 552 * j + c) % 3 = c % 3 := by omega
    have g : ∀ r < 4, (B[4 * (5 + 184 * j + c / 3) + r]?).getD 0 = chAt p.1 (4 * (c / 3) + r) := by
      intro r hr
      have e : 4 * (5 + 184 * j + c / 3) + r = 20 + 736 * j + (4 * (c / 3) + r) := by omega
      rw [e]
      exact hGL j p (by omega) hp _ (by omega)
    rw [hbyte _ (by omega), testBit_Db _ _ _ hi, e1, e2, hDq,
      ← Nat.add_zero (4 * (5 + 184 * j + c / 3)), g 0 (by omega), g 1 (by omega), g 2 (by omega),
      g 3 (by omega), Nat.add_zero, ← quadV_eq,
      ← testBit_segDec_byte p.1 184 c i (by omega) hi, hsd]
  by_cases hb : t / 8 < 551
  · have e : 16 + 552 * k + t / 8 = 15 + 552 * k + (t / 8 + 1) := by omega
    have et : 8 * (t / 8 + 1 - 1) + t % 8 = t := by omega
    have ht' : t < 4408 := by omega
    rw [e, hchunk k hk _ (by omega) _ (Nat.mod_lt _ (by omega)),
      testBit_segWant_hi R k _ _ (by omega) (Nat.mod_lt _ (by omega)), et]
    simp [ht']
  by_cases hk' : k < 4369
  · have e : 16 + 552 * k + t / 8 = 15 + 552 * (k + 1) + 0 := by omega
    have et : 4408 + t % 8 = t := by omega
    rw [e, hchunk (k + 1) (by omega) 0 (by omega) _ (Nat.mod_lt _ (by omega)), Nat.mul_zero,
      Nat.zero_add, testBit_segWant_lo R k _ (Nat.mod_lt _ (by omega)), et]
  · have ek : k = 4369 := by omega
    subst ek
    have e : 16 + 552 * 4369 + t / 8 = 2412255 := by omega
    have et : 4408 + t % 8 = t := by omega
    have hi : t % 8 < 8 := Nat.mod_lt _ (by omega)
    have g : ∀ r < 2, (B[4 * 804085 + r]?).getD 0 = chAt pl.1 r := by
      intro r hr
      have e : 4 * 804085 + r = 20 + 736 * 4370 + r := by omega
      rw [e]
      exact hGL 4370 pl (Nat.le_refl _) hpl r (by omega)
    have e1 : 2412255 / 3 = 804085 := by omega
    have e2 : 2412255 % 3 = 0 := by omega
    rw [e, hbyte _ (by omega), testBit_Db _ _ _ hi, e1, e2, hDq, Nat.mul_zero, Nat.sub_zero,
      ← Nat.add_zero (4 * 804085), g 0 (by omega), g 1 (by omega), Nat.add_zero,
      quad4_hi (b64v_lt _ (hG _)) (b64v_lt _ (hG _)) (b64v_lt _ (chAt_lt pl.1 2))
        (b64v_lt _ (chAt_lt pl.1 3)), ← quadV_eq pl.1 0,
      ← Nat.sub_zero 16, ← Nat.mul_zero 8, ← Nat.zero_mod 3, ← Nat.zero_div 3,
      ← testBit_segDec_byte pl.1 1 0 _ (by omega) hi, Nat.mul_zero, Nat.zero_add,
      ← testBit_land255 _ _ hi, hpl1, testBit_lastByte, et]
    simp [hi]

end CFSG.KC.BM.B64

end
