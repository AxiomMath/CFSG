module

public import CFSG.Certificates.Kernel.Spor.PK.F42Mat
public import CFSG.Certificates.Kernel.Spor.PK.Str
import all Init.Data.String.Slice
import all Init.Data.String.Search
public import CFSG.Certificates.Kernel.Misc.F42Defs

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.F3.Native
open CFSG.LieType.Multipliers.F42 (parseInts)

namespace F42Parse

private theorem beq_false_of_ne' {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')

private theorem ble_true {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by
  rw [← Nat.ble_eq] at h
  exact h

private theorem ble_false {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  rw [Bool.eq_false_iff]
  intro h'
  rw [Nat.ble_eq] at h'
  exact h h'

private theorem testBit_false_of_lt_pow {N k b : ℕ} (h : N < 2 ^ k) (hb : k ≤ b) :
    N.testBit b = false :=
  Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right Nat.two_pos hb))

end F42Parse

open F42Parse

theorem wsK_iff (c : ℕ) :
    wsK c = true ↔ c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 11 ∨ c = 12 := by
  simp only [wsK, orB_eq, Bool.or_eq_true, Nat.beq_eq]

theorem entryK_eq (c : ℕ) : entryK c = if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0 := by
  unfold entryK
  have : andB (Nat.ble 48 c) (Nat.ble c 57) = decide (48 ≤ c ∧ c ≤ 57) := by
    rw [Bool.eq_iff_iff]
    simp [andB_eq, Nat.ble_eq]
  rw [this]
  by_cases h : 48 ≤ c ∧ c ≤ 57
  · rw [decide_eq_true h, if_pos h]
    rfl
  · rw [decide_eq_false h, if_neg h]

theorem afterNL_eq (cs : List ℕ) : afterNL cs = (cs.dropWhile fun c => c != 10).drop 1 := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    show Bool.rec (motive := fun _ => List Nat) (afterNL t) t (Nat.beq c 10) = _
    by_cases h : c = 10
    · subst h
      simp
    · rw [beq_false_of_ne' h]
      simp [List.dropWhile_cons, h, ih]

@[expose] def f42Entries (cs : List ℕ) : List ℕ :=
  (((cs.dropWhile fun c => c != 10).drop 1).filter fun c =>
      !(c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12)).map fun c =>
    if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0

namespace F42Parse

private theorem ofNat_toNat_cases (c : ℕ) :
    ((Char.ofNat c).toNat = c ∨ (Char.ofNat c).toNat = 0) ∧
      (c < 128 → (Char.ofNat c).toNat = c) := by
  unfold Char.ofNat
  split
  · exact ⟨Or.inl rfl, fun _ => rfl⟩
  · rename_i h
    exact ⟨Or.inr rfl, fun hc => absurd (Or.inl (by omega)) h⟩

private theorem ofNat_eq_char {c : ℕ} {d : Char} (hd : 0 < d.toNat) (hd' : d.toNat < 128) :
    Char.ofNat c = d ↔ c = d.toNat := by
  rw [← Char.toNat_inj]
  obtain ⟨h1, h2⟩ := ofNat_toNat_cases c
  constructor
  · intro h
    omega
  · intro h
    rw [h, Char.ofNat_toNat]

private theorem ne_nl_ofNat (c : ℕ) : (Char.ofNat c != '\n') = (c != 10) := by
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq]
  rw [ofNat_eq_char (d := '\n') (by decide) (by decide)]
  rfl

private theorem wsChar_ofNat (c : ℕ) :
    wsChar (Char.ofNat c) = (c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12) := by
  rw [Bool.eq_iff_iff]
  simp only [wsChar, Bool.or_eq_true, beq_iff_eq]
  rw [ofNat_eq_char (d := ' ') (by decide) (by decide),
    ofNat_eq_char (d := '\t') (by decide) (by decide),
    ofNat_eq_char (d := '\n') (by decide) (by decide),
    ofNat_eq_char (d := '\r') (by decide) (by decide)]
  obtain ⟨h1, h2⟩ := ofNat_toNat_cases c
  have e1 : ' '.toNat = 32 := rfl
  have e2 : '\t'.toNat = 9 := rfl
  have e3 : '\n'.toNat = 10 := rfl
  have e4 : '\r'.toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  omega

private theorem digit_ofNat (c : ℕ) :
    (if (decide ('0' ≤ Char.ofNat c) && decide (Char.ofNat c ≤ '9')) = true then
        (Char.ofNat c).toNat - '0'.toNat else 0) = if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0 := by
  obtain ⟨h1, h2⟩ := ofNat_toNat_cases c
  have e0 : '0'.toNat = 48 := rfl
  have e9 : '9'.toNat = 57 := rfl
  have hc : ((decide ('0' ≤ Char.ofNat c) && decide (Char.ofNat c ≤ '9')) = true) ↔
      (48 ≤ c ∧ c ≤ 57) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
      Char.toNat_val]
    rw [e0, e9]
    omega
  by_cases h : 48 ≤ c ∧ c ≤ 57
  · rw [if_pos (hc.2 h), if_pos h, e0]
    omega
  · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]

end F42Parse

theorem decodeEntries_strL (cs : List ℕ) : decodeEntries (strL cs) = f42Entries cs := by
  unfold decodeEntries f42Entries
  have h1 : (strL cs).toList = cs.map Char.ofNat := by simp [strL]
  dsimp only
  rw [h1, List.dropWhile_map, ← List.map_drop, List.filter_map, List.map_map]
  have e1 : ((fun x : Char => x != '\n') ∘ Char.ofNat) = fun c : ℕ => c != 10 := by
    funext c
    exact ne_nl_ofNat c
  have e2 : ((fun c : Char => !wsChar c) ∘ Char.ofNat) =
      fun c : ℕ => !(c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12) := by
    funext c
    simp only [Function.comp_apply, wsChar_ofNat]
  have e3 : ((fun c : Char => if (decide ('0' ≤ c) && decide (c ≤ '9')) = true then
      c.toNat - '0'.toNat else 0) ∘ Char.ofNat) =
      fun c : ℕ => if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0 := by
    funext c
    exact digit_ofNat c
  rw [e1, e2, e3]

namespace F42Parse

private noncomputable def decR (l : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun c _ ih i acc => Bool.rec (motive := fun _ => ℕ)
      (letN (Nat.mod (entryK c) 3) fun v => ih (Nat.succ i) (Bool.rec (motive := fun _ => ℕ)
        acc (Nat.lor acc (Nat.shiftLeft 1
          (Bool.rec (motive := fun _ => ℕ) i (Nat.add i 2704) (Nat.beq v 2))))
        (andB (Nat.blt 0 v) (Nat.blt i 2704))))
      (ih i acc) (wsK c)) l

private theorem decodeK_eq_decR (cs : List ℕ) : decodeK cs = decR (afterNL cs) 0 0 := rfl

private def entStep (i acc v : ℕ) : ℕ :=
  if 0 < v ∧ i < 2704 then acc ||| 1 <<< (if v = 2 then i + 2704 else i) else acc

private theorem decR_cons (c : ℕ) (l : List ℕ) (i acc : ℕ) :
    decR (c :: l) i acc = Bool.rec (motive := fun _ => ℕ)
      (letN (Nat.mod (entryK c) 3) fun v => decR l (Nat.succ i) (Bool.rec (motive := fun _ => ℕ)
        acc (Nat.lor acc (Nat.shiftLeft 1
          (Bool.rec (motive := fun _ => ℕ) i (Nat.add i 2704) (Nat.beq v 2))))
        (andB (Nat.blt 0 v) (Nat.blt i 2704))))
      (decR l i acc) (wsK c) := rfl

private theorem decR_ws {c : ℕ} (h : wsK c = true) (l : List ℕ) (i acc : ℕ) :
    decR (c :: l) i acc = decR l i acc := by
  rw [decR_cons, h]

private theorem decR_ent {c : ℕ} (h : wsK c = false) (l : List ℕ) (i acc : ℕ) :
    decR (c :: l) i acc = decR l (i + 1) (entStep i acc (entryK c % 3)) := by
  rw [decR_cons, h]
  show letN (Nat.mod (entryK c) 3) _ = _
  rw [letN_eq]
  show decR l (Nat.succ i) _ = _
  congr 1
  unfold entStep
  have e1 : Nat.mod (entryK c) 3 = entryK c % 3 := rfl
  rw [e1]
  generalize entryK c % 3 = v
  by_cases h1 : 0 < v ∧ i < 2704
  · have : andB (Nat.blt 0 v) (Nat.blt i 2704) = true := by
      simp [andB_eq, Nat.blt_eq, h1]
    rw [this, if_pos h1]
    by_cases h2 : v = 2
    · subst h2
      simp
    · rw [beq_false_of_ne' h2, if_neg h2]
      rfl
  · have : andB (Nat.blt 0 v) (Nat.blt i 2704) = false := by
      rw [Bool.eq_false_iff]
      simpa [andB_eq, Nat.blt_eq] using h1
    rw [this, if_neg h1]

private def entFold : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | e :: t, i, acc => entFold t (i + 1) (entStep i acc (e % 3))

private theorem decR_eq_entFold (l : List ℕ) :
    ∀ i acc, decR l i acc = entFold ((l.filter fun c => !wsK c).map entryK) i acc := by
  induction l with
  | nil =>
    intro i acc
    rfl
  | cons c t ih =>
    intro i acc
    by_cases h : wsK c = true
    · rw [decR_ws h, ih]
      simp [h]
    · have h' : wsK c = false := by simpa using h
      rw [decR_ent h', ih]
      simp [h', entFold]

private def entBit (G : List ℕ) (i b : ℕ) : Bool :=
  (decide (i ≤ b) && decide (b < 2704) && decide (G.getD b 0 % 3 = 1)) ||
  (decide (2704 + i ≤ b) && decide (b < 5408) && decide (G.getD (b - 2704) 0 % 3 = 2))

private theorem entStep_testBit (i acc v b : ℕ) :
    (entStep i acc v).testBit b =
      (acc.testBit b || decide (0 < v ∧ i < 2704 ∧ b = if v = 2 then i + 2704 else i)) := by
  unfold entStep
  by_cases h : 0 < v ∧ i < 2704
  · rw [if_pos h, Nat.testBit_or, testBit_one_shiftLeft]
    simp only [h, true_and, decide_eq_true_eq]
  · rw [if_neg h]
    have : ¬ (0 < v ∧ i < 2704 ∧ b = if v = 2 then i + 2704 else i) :=
      fun ⟨h1, h2, _⟩ => h ⟨h1, h2⟩
    rw [decide_eq_false this]
    simp

private theorem entBit_step (G : List ℕ) (i b : ℕ) :
    entBit G i b = (decide (0 < G.getD i 0 % 3 ∧ i < 2704 ∧
        b = if G.getD i 0 % 3 = 2 then i + 2704 else i) || entBit G (i + 1) b) := by
  rw [Bool.eq_iff_iff]
  simp only [entBit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hbi : b = i
  · subst hbi
    have : ¬ (2704 + b ≤ b) := by omega
    simp only [this, false_and, and_false, or_false]
    split_ifs <;> omega
  · by_cases hbm : b = i + 2704
    · subst hbm
      simp only [Nat.add_sub_cancel]
      split_ifs <;> omega
    · split_ifs <;> omega

private theorem getD_of_le {G : List ℕ} {b : ℕ} (h : G.length ≤ b) : G.getD b 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem entFold_testBit (G : List ℕ) : ∀ (n i acc : ℕ), i + n = G.length → ∀ b,
    (entFold (G.drop i) i acc).testBit b = (acc.testBit b || entBit G i b) := by
  intro n
  induction n with
  | zero =>
    intro i acc hi b
    rw [List.drop_eq_nil_of_le (by omega)]
    have : entBit G i b = false := by
      unfold entBit
      rw [Bool.eq_false_iff]
      simp only [ne_eq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rw [getD_of_le (by omega)] at h3
        simp at h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rw [getD_of_le (by omega)] at h3
        simp at h3
    rw [this]
    simp [entFold]
  | succ n ih =>
    intro i acc hi b
    have hlt : i < G.length := by omega
    rw [List.drop_eq_getElem_cons hlt]
    show (entFold (G.drop (i + 1)) (i + 1) (entStep i acc (G[i] % 3))).testBit b = _
    rw [ih (i + 1) _ (by omega) b, entStep_testBit, entBit_step G i b]
    have : G.getD i 0 = G[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rw [this]
    simp [Bool.or_assoc]

private theorem wsK_eq (c : ℕ) :
    wsK c = (c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12) := by
  rw [Bool.eq_iff_iff, wsK_iff]
  simp only [Bool.or_eq_true, beq_iff_eq]
  tauto

private theorem entries_eq (cs : List ℕ) :
    ((afterNL cs).filter fun c => !wsK c).map entryK = f42Entries cs := by
  rw [afterNL_eq]
  unfold f42Entries
  have e1 : (fun c : ℕ => !wsK c) =
      fun c => !(c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12) := by
    funext c
    rw [wsK_eq]
  have e2 : entryK = fun c : ℕ => if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0 := by
    funext c
    exact entryK_eq c
  rw [e1, e2]

private theorem decodeK_testBit (cs : List ℕ) (b : ℕ) :
    (decodeK cs).testBit b = entBit (f42Entries cs) 0 b := by
  rw [decodeK_eq_decR, decR_eq_entFold, entries_eq]
  have := entFold_testBit (f42Entries cs) (f42Entries cs).length 0 0 (by simp) b
  rw [List.drop_zero] at this
  rw [this]
  simp

end F42Parse

theorem decodeK_entries (cs : List ℕ) :
    decodeK cs = pk52 (Array.ofFn (n := 52) fun i =>
      V.ofFn 52 fun j => (f42Entries cs).getD (52 * i.val + j) 0) := by
  generalize hG : f42Entries cs = G
  generalize hX : (Array.ofFn (n := 52) fun i => V.ofFn 52 fun j => G.getD (52 * i.val + j) 0) = X
  have hsize : X.size = 52 := by
    rw [← hX]
    simp
  have hrow : ∀ i < 52, X[i]! = V.ofFn 52 (fun j => G.getD (52 * i + j) 0) := by
    intro i hi
    subst hX
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  have hp : ∀ i < 52, ∀ j, X[i]!.p.testBit j =
      (decide (j < 52) && decide (G.getD (52 * i + j) 0 % 3 = 1)) := by
    intro i hi j
    rw [hrow i hi]
    exact (fold_ofFnStep_bits _ j 52).1
  have hm : ∀ i < 52, ∀ j, X[i]!.m.testBit j =
      (decide (j < 52) && decide (G.getD (52 * i + j) 0 % 3 = 2)) := by
    intro i hi j
    rw [hrow i hi]
    exact (fold_ofFnStep_bits _ j 52).2
  have hcan : Can52 X := by
    refine can52_iff.2 ⟨hsize, fun i hi => ⟨?_, ?_, ?_⟩⟩
    · apply Nat.lt_pow_two_of_testBit
      intro j hj
      rw [hp i hi j]
      simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
      omega
    · apply Nat.lt_pow_two_of_testBit
      intro j hj
      rw [hm i hi j]
      simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
      omega
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, hp i hi j, hm i hi j, Nat.zero_testBit]
      generalize G.getD (52 * i + j) 0 = x
      by_cases h1 : x % 3 = 1
      · have : ¬ x % 3 = 2 := by omega
        simp [h1, this]
      · simp [h1]
  apply Nat.eq_of_testBit_eq
  intro b
  have hd := decodeK_testBit cs b
  rw [hG] at hd
  rw [hd]
  by_cases hb1 : b < 2704
  · have hi : b / 52 < 52 := by omega
    have hj : b % 52 < 52 := by omega
    have hb : b = 52 * (b / 52) + b % 52 := by omega
    have h1 := testBit_pk52_p hcan hi hj
    rw [← hb, hp _ hi] at h1
    rw [h1]
    unfold entBit
    have : ¬ (2704 + 0 ≤ b) := by omega
    simp [hb1, this, ← hb, hj]
  · by_cases hb2 : b < 5408
    · have hi : (b - 2704) / 52 < 52 := by omega
      have hj : (b - 2704) % 52 < 52 := by omega
      have hb : b - 2704 = 52 * ((b - 2704) / 52) + (b - 2704) % 52 := by omega
      have h1 := testBit_pk52_m hcan hi hj
      rw [← hb, hm _ hi, show 2704 + (b - 2704) = b by omega] at h1
      rw [h1]
      unfold entBit
      simp [hb1, hb2, ← hb, hj]
      omega
    · have h1 : (pk52 X).testBit b = false := testBit_false_of_lt_pow (pk52_lt hcan) (by omega)
      rw [h1]
      unfold entBit
      simp
      omega

namespace F42Parse

private theorem rowsOf_strL (cs : List ℕ) :
    CFSG.F3.Native.rowsOf 52 (strL cs) = Array.ofFn (n := 52) fun i =>
      V.ofFn 52 fun j => (f42Entries cs).getD (52 * i.val + j) 0 := by
  unfold CFSG.F3.Native.rowsOf
  rw [decodeEntries_strL]
  refine congrArg (fun f : Fin 52 → V => Array.ofFn (n := 52) f) ?_
  funext i
  refine congrArg (V.ofFn 52) ?_
  funext j
  simp [List.getElem?_toArray, List.getD_eq_getElem?_getD, Nat.mul_comm]

end F42Parse

theorem decodeK_eq (cs : List ℕ) : decodeK cs = pk52 (rowsOf 52 (strL cs)) := by
  rw [rowsOf_strL]
  exact decodeK_entries cs

@[expose] def F42Tok (l : List ℕ) : Prop := IsDigits l ∨ ∃ ds, IsDigits ds ∧ l = 45 :: ds

@[expose] def f42TokCode : List ℕ → ℕ
  | 45 :: ds => if decVal ds = 0 then 0 else 2 * (decVal ds - 1) + 1
  | ds => 2 * decVal ds

@[expose] def f42Sep (c : ℕ) : Bool := c == 32 || c == 10

@[expose] def f42Toks (cs : List ℕ) : List (List ℕ) := (cs.splitOnP f42Sep).filter fun t => t != []

namespace F42Parse

private theorem modifyHead_map {α β : Type} (f : α → β) (x : α) (L : List (List α)) :
    (L.modifyHead (List.cons x)).map (List.map f) =
      (L.map (List.map f)).modifyHead (List.cons (f x)) := by
  cases L <;> simp

private theorem splitOnP_map {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).splitOnP p = (l.splitOnP (p ∘ f)).map (List.map f) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.splitOnP_cons_eq_ite_modifyHead, List.splitOnP_cons_eq_ite_modifyHead,
      ih]
    by_cases h : p (f x) = true
    · simp [h]
    · simp [h, modifyHead_map]

private theorem sep_ofNat (c : ℕ) :
    ((fun ch : Char => ch == ' ' || ch == '\n') (Char.ofNat c)) = f42Sep c := by
  unfold f42Sep
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, beq_iff_eq]
  rw [ofNat_eq_char (d := ' ') (by decide) (by decide),
    ofNat_eq_char (d := '\n') (by decide) (by decide)]
  rfl

end F42Parse

theorem parseInts_strL (cs : List ℕ) :
    parseInts (strL cs) = (cs.splitOnP f42Sep).filterMap fun t => (strL t).toInt? := by
  unfold parseInts
  have h := String.toList_split_bool (s := strL cs) (p := fun c => c == ' ' || c == '\n')
  have e1 : (fun t : String.Slice => t.toString.toInt?) =
      (fun s : String => s.toInt?) ∘ String.Slice.copy := by
    funext t
    simp only [Function.comp_apply, String.Slice.toString_eq]
  rw [e1, ← List.filterMap_map, h]
  have h1 : (strL cs).toList = cs.map Char.ofNat := by simp [strL]
  rw [h1, splitOnP_map, List.map_map, List.filterMap_map]
  have e2 : (fun ch : Char => ch == ' ' || ch == '\n') ∘ Char.ofNat = f42Sep :=
    funext sep_ofNat
  rw [e2]
  rfl

theorem toInt?_f42Tok {t : List ℕ} (h : F42Tok t) :
    (strL t).toInt? = some (refOfCode (f42TokCode t)) := by
  rcases h with hd | ⟨ds, hds, rfl⟩
  · rw [toInt?_strL hd]
    have e : f42TokCode t = 2 * decVal t := by
      obtain ⟨hne, hall⟩ := hd
      cases t with
      | nil => exact absurd rfl hne
      | cons d l =>
        have := hall d (by simp)
        have hd45 : d ≠ 45 := by omega
        simp [f42TokCode, hd45]
    rw [e]
    simp [refOfCode]
  · rw [toInt?_strL_neg hds]
    simp only [f42TokCode]
    by_cases hv : decVal ds = 0
    · simp [hv, refOfCode]
    · rw [if_neg hv]
      simp only [refOfCode]
      have h2 : (2 * (decVal ds - 1) + 1) / 2 = decVal ds - 1 := by omega
      rw [if_neg (by omega), h2]
      have : 1 ≤ decVal ds := by omega
      congr 1
      omega

namespace F42Parse

private theorem isNat_nil (t : String.Slice) (h : t.copy.toList = []) : t.isNat = false := by
  unfold String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList, h]
  rfl

end F42Parse

theorem toInt?_strL_nil : (strL []).toInt? = none := by
  show (strL []).toSlice.toInt? = none
  unfold String.Slice.toInt?
  have h0 : (strL []).toSlice.copy.toList = [] := by
    rw [String.copy_toSlice]
    simp [strL]
  have h1 : (strL []).toSlice.dropPrefix? '-' = none := by
    rw [String.Slice.dropPrefix?_eq_none_iff, String.Slice.startsWith_char_eq_head?, h0]
    simp
  rw [h1]
  have h2 : (strL []).toSlice.toNat? = none := by
    unfold String.Slice.toNat?
    rw [isNat_nil _ h0]
    rfl
  rw [h2]
  rfl

namespace F42Parse

private noncomputable def fmtRun (cs : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun st => notB (Nat.beq st 1))
    (fun c _ ih st => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (andB (Nat.beq st 0) (ih 1)) (Nat.beq c 45))
        (ih 2) (andB (Nat.ble 48 c) (Nat.ble c 57)))
      (andB (notB (Nat.beq st 1)) (ih 0)) (orB (Nat.beq c 32) (Nat.beq c 10))) cs

private noncomputable def intsRun (cs : List ℕ) : ℕ → List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ)
    (fun st => Bool.rec (motive := fun _ => List ℕ) List.nil
      [intsK.codeOf st] (Nat.ble 2 st))
    (fun c _ ih st => Bool.rec (motive := fun _ => List ℕ)
      (Bool.rec (motive := fun _ => List ℕ) (ih 1)
        (letLN (Nat.add (Nat.mul 10 (intsK.valOf st)) (Nat.sub c 48)) fun v =>
          ih (Nat.add 2 (Nat.add (Nat.mul 2 v) (intsK.signOf st))))
        (andB (Nat.ble 48 c) (Nat.ble c 57)))
      (Bool.rec (motive := fun _ => List ℕ) (ih 0) (List.cons (intsK.codeOf st) (ih 0))
        (Nat.ble 2 st))
      (orB (Nat.beq c 32) (Nat.beq c 10))) cs

private theorem fmtK_eq_run (cs : List ℕ) : fmtK cs = fmtRun cs 0 := rfl

private theorem intsK_eq_run (cs : List ℕ) : intsK cs = intsRun cs 0 := rfl

private theorem fmtRun_nil (st : ℕ) : fmtRun [] st = !(Nat.beq st 1) := rfl

private theorem fmtRun_sep {c : ℕ} (hc : c = 32 ∨ c = 10) (cs : List ℕ) (st : ℕ) :
    fmtRun (c :: cs) st = (!(Nat.beq st 1) && fmtRun cs 0) := by
  have : orB (Nat.beq c 32) (Nat.beq c 10) = true := by
    rcases hc with rfl | rfl <;> rfl
  show Bool.rec (motive := fun _ => Bool) _ _ (orB (Nat.beq c 32) (Nat.beq c 10)) = _
  rw [this]
  exact andB_eq _ _

private theorem fmtRun_digit {c : ℕ} (hc : 48 ≤ c ∧ c ≤ 57) (cs : List ℕ) (st : ℕ) :
    fmtRun (c :: cs) st = fmtRun cs 2 := by
  have h1 : orB (Nat.beq c 32) (Nat.beq c 10) = false := by
    rw [orB_eq, Bool.or_eq_false_iff]
    exact ⟨beq_false_of_ne' (by omega), beq_false_of_ne' (by omega)⟩
  have h2 : andB (Nat.ble 48 c) (Nat.ble c 57) = true := by
    simp [andB_eq, Nat.ble_eq, hc]
  show Bool.rec (motive := fun _ => Bool) _ _ (orB (Nat.beq c 32) (Nat.beq c 10)) = _
  rw [h1]
  show Bool.rec (motive := fun _ => Bool) _ _ (andB (Nat.ble 48 c) (Nat.ble c 57)) = _
  rw [h2]
  rfl

private theorem fmtRun_minus (cs : List ℕ) (st : ℕ) :
    fmtRun (45 :: cs) st = (Nat.beq st 0 && fmtRun cs 1) := rfl

private theorem fmtRun_other {c : ℕ} (h1 : c ≠ 32) (h2 : c ≠ 10) (h3 : ¬ (48 ≤ c ∧ c ≤ 57))
    (h4 : c ≠ 45) (cs : List ℕ) (st : ℕ) : fmtRun (c :: cs) st = false := by
  have e1 : orB (Nat.beq c 32) (Nat.beq c 10) = false := by
    rw [orB_eq, Bool.or_eq_false_iff]
    exact ⟨beq_false_of_ne' h1, beq_false_of_ne' h2⟩
  have e2 : andB (Nat.ble 48 c) (Nat.ble c 57) = false := by
    rw [Bool.eq_false_iff]
    simpa [andB_eq, Nat.ble_eq] using h3
  show Bool.rec (motive := fun _ => Bool) _ _ (orB (Nat.beq c 32) (Nat.beq c 10)) = _
  rw [e1]
  show Bool.rec (motive := fun _ => Bool) _ _ (andB (Nat.ble 48 c) (Nat.ble c 57)) = _
  rw [e2]
  show Bool.rec (motive := fun _ => Bool) _ _ (Nat.beq c 45) = _
  rw [beq_false_of_ne' h4]

private theorem intsRun_nil (st : ℕ) :
    intsRun [] st = if 2 ≤ st then [intsK.codeOf st] else [] := by
  show Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.ble 2 st) = _
  by_cases h : 2 ≤ st
  · rw [if_pos h, ble_true h]
  · rw [if_neg h, ble_false h]

private theorem intsRun_sep {c : ℕ} (hc : c = 32 ∨ c = 10) (cs : List ℕ) (st : ℕ) :
    intsRun (c :: cs) st = (if 2 ≤ st then [intsK.codeOf st] else []) ++ intsRun cs 0 := by
  have : orB (Nat.beq c 32) (Nat.beq c 10) = true := by
    rcases hc with rfl | rfl <;> rfl
  show Bool.rec (motive := fun _ => List ℕ) _ _ (orB (Nat.beq c 32) (Nat.beq c 10)) = _
  rw [this]
  show Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.ble 2 st) = _
  by_cases h : 2 ≤ st
  · rw [if_pos h, ble_true h]
    rfl
  · rw [if_neg h, ble_false h]
    rfl

private theorem intsRun_digit {c : ℕ} (hc : 48 ≤ c ∧ c ≤ 57) (cs : List ℕ) (st : ℕ) :
    intsRun (c :: cs) st =
      intsRun cs (2 + (2 * (10 * intsK.valOf st + (c - 48)) + intsK.signOf st)) := by
  have h1 : orB (Nat.beq c 32) (Nat.beq c 10) = false := by
    rw [orB_eq, Bool.or_eq_false_iff]
    exact ⟨beq_false_of_ne' (by omega), beq_false_of_ne' (by omega)⟩
  have h2 : andB (Nat.ble 48 c) (Nat.ble c 57) = true := by
    simp [andB_eq, Nat.ble_eq, hc]
  show Bool.rec (motive := fun _ => List ℕ) _ _ (orB (Nat.beq c 32) (Nat.beq c 10)) = _
  rw [h1]
  show Bool.rec (motive := fun _ => List ℕ) _ _ (andB (Nat.ble 48 c) (Nat.ble c 57)) = _
  rw [h2]
  show letLN _ _ = _
  rw [letLN_eq]
  rfl

private theorem intsRun_other {c : ℕ} (h1 : c ≠ 32) (h2 : c ≠ 10) (h3 : ¬ (48 ≤ c ∧ c ≤ 57))
    (cs : List ℕ) (st : ℕ) : intsRun (c :: cs) st = intsRun cs 1 := by
  have e1 : orB (Nat.beq c 32) (Nat.beq c 10) = false := by
    rw [orB_eq, Bool.or_eq_false_iff]
    exact ⟨beq_false_of_ne' h1, beq_false_of_ne' h2⟩
  have e2 : andB (Nat.ble 48 c) (Nat.ble c 57) = false := by
    rw [Bool.eq_false_iff]
    simpa [andB_eq, Nat.ble_eq] using h3
  show Bool.rec (motive := fun _ => List ℕ) _ _ (orB (Nat.beq c 32) (Nat.beq c 10)) = _
  rw [e1]
  show Bool.rec (motive := fun _ => List ℕ) _ _ (andB (Nat.ble 48 c) (Nat.ble c 57)) = _
  rw [e2]
  rfl

private def fmtSt (ng : Bool) (ds : List ℕ) : ℕ := if ds = [] then (if ng then 1 else 0) else 2

private def intsSt (ng : Bool) (ds : List ℕ) : ℕ :=
  if ds = [] then (if ng then 1 else 0) else 2 + 2 * decVal ds + (if ng then 1 else 0)

private def tokPre (ng : Bool) (ds : List ℕ) : List ℕ := (if ng then [45] else []) ++ ds

private theorem decVal_snoc (ds : List ℕ) (c : ℕ) :
    decVal (ds ++ [c]) = 10 * decVal ds + (c - 48) := by
  simp [decVal, List.foldl_append]

private theorem valOf_lt {st : ℕ} (h : st < 2) : intsK.valOf st = 0 := by
  show Bool.rec (motive := fun _ => ℕ) 0 _ (Nat.ble 2 st) = 0
  rw [ble_false (by omega)]

private theorem valOf_ge {st : ℕ} (h : 2 ≤ st) : intsK.valOf st = (st - 2) / 2 := by
  show Bool.rec (motive := fun _ => ℕ) 0 _ (Nat.ble 2 st) = _
  rw [ble_true h]
  rfl

private theorem signOf_one : intsK.signOf 1 = 1 := rfl

private theorem signOf_zero : intsK.signOf 0 = 0 := rfl

private theorem signOf_ge {st : ℕ} (h : 2 ≤ st) : intsK.signOf st = (st - 2) % 2 := by
  show Bool.rec (motive := fun _ => ℕ) _ 1 (Nat.beq st 1) = _
  rw [beq_false_of_ne' (by omega)]
  rfl

private theorem codeOf_ge {st : ℕ} (h : 2 ≤ st) : intsK.codeOf st =
    if (st - 2) % 2 = 1 ∧ 0 < (st - 2) / 2 then 2 * ((st - 2) / 2 - 1) + 1
    else 2 * ((st - 2) / 2) := by
  show Bool.rec (motive := fun _ => ℕ) _ _
    (andB (Nat.beq (Nat.mod (Nat.sub st 2) 2) 1) (Nat.blt 0 (intsK.valOf st))) = _
  rw [valOf_ge h]
  have e : Nat.mod (Nat.sub st 2) 2 = (st - 2) % 2 := rfl
  rw [e]
  by_cases h1 : (st - 2) % 2 = 1 ∧ 0 < (st - 2) / 2
  · have : andB (Nat.beq ((st - 2) % 2) 1) (Nat.blt 0 ((st - 2) / 2)) = true := by
      simp [andB_eq, Nat.blt_eq, Nat.beq_eq, h1]
    rw [this, if_pos h1]
    rfl
  · have : andB (Nat.beq ((st - 2) % 2) 1) (Nat.blt 0 ((st - 2) / 2)) = false := by
      rw [Bool.eq_false_iff]
      simpa [andB_eq, Nat.blt_eq, Nat.beq_eq] using h1
    rw [this, if_neg h1]
    rfl

private theorem intsSt_nil (ng : Bool) : intsSt ng [] = if ng then 1 else 0 := by
  simp [intsSt]

private theorem intsSt_ne {ds : List ℕ} (h : ds ≠ []) (ng : Bool) :
    intsSt ng ds = 2 + 2 * decVal ds + (if ng then 1 else 0) := by
  simp [intsSt, h]

private theorem valOf_intsSt_nil (ng : Bool) : intsK.valOf (intsSt ng []) = 0 := by
  rw [intsSt_nil]
  exact valOf_lt (by cases ng <;> simp)

private theorem signOf_intsSt_nil (ng : Bool) :
    intsK.signOf (intsSt ng []) = if ng then 1 else 0 := by
  rw [intsSt_nil]
  cases ng
  · exact signOf_zero
  · exact signOf_one

private theorem valOf_intsSt (ng : Bool) {ds : List ℕ} (h : ds ≠ []) :
    intsK.valOf (intsSt ng ds) = decVal ds := by
  rw [intsSt_ne h, valOf_ge (by omega)]
  cases ng <;> simp <;> omega

private theorem signOf_intsSt (ng : Bool) {ds : List ℕ} (h : ds ≠ []) :
    intsK.signOf (intsSt ng ds) = if ng then 1 else 0 := by
  rw [intsSt_ne h, signOf_ge (by omega)]
  cases ng <;> simp <;> omega

private theorem codeOf_intsSt (ng : Bool) {ds : List ℕ} (h : ds ≠ []) :
    intsK.codeOf (intsSt ng ds) =
      if ng then (if decVal ds = 0 then 0 else 2 * (decVal ds - 1) + 1) else 2 * decVal ds := by
  rw [intsSt_ne h, codeOf_ge (by omega)]
  cases ng
  · simp only [Bool.false_eq_true, if_false]
    rw [if_neg (by omega)]
    omega
  · simp only [if_true]
    by_cases hv : decVal ds = 0
    · rw [if_neg (by omega), if_pos hv]
      omega
    · rw [if_pos (by omega), if_neg hv]
      omega

private theorem intsSt_digit (ng : Bool) (ds : List ℕ) {c : ℕ} (hc : 48 ≤ c ∧ c ≤ 57) :
    2 + (2 * (10 * intsK.valOf (intsSt ng ds) + (c - 48)) + intsK.signOf (intsSt ng ds)) =
      intsSt ng (ds ++ [c]) := by
  have hne : ds ++ [c] ≠ [] := by simp
  rw [intsSt_ne hne, decVal_snoc]
  by_cases hd : ds = []
  · subst hd
    rw [valOf_intsSt_nil, signOf_intsSt_nil]
    simp [decVal]
    omega
  · rw [valOf_intsSt ng hd, signOf_intsSt ng hd]
    omega

private theorem fmtSt_ne {ng : Bool} {ds : List ℕ} (h : ds ≠ []) : fmtSt ng ds = 2 := by
  simp [fmtSt, h]

private theorem tokPre_snoc (ng : Bool) (ds : List ℕ) (c : ℕ) (cs : List ℕ) :
    tokPre ng (ds ++ [c]) ++ cs = tokPre ng ds ++ c :: cs := by
  simp [tokPre, List.append_assoc]

private theorem tokPre_nosep (ng : Bool) {ds : List ℕ} (hds : ∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57) :
    ∀ x ∈ tokPre ng ds, f42Sep x = false := by
  intro x hx
  have h1 : x = 45 ∨ x ∈ ds := by
    unfold tokPre at hx
    cases ng
    · exact Or.inr (by simpa using hx)
    · simpa using hx
  unfold f42Sep
  rcases h1 with rfl | h1
  · decide
  · have := hds x h1
    rw [Bool.or_eq_false_iff]
    exact ⟨by simpa using (by omega : x ≠ 32), by simpa using (by omega : x ≠ 10)⟩

private theorem f42TokCode_tokPre (ng : Bool) {ds : List ℕ} (hd : IsDigits ds) :
    f42TokCode (tokPre ng ds) =
      if ng then (if decVal ds = 0 then 0 else 2 * (decVal ds - 1) + 1) else 2 * decVal ds := by
  cases ng
  · obtain ⟨hne, hall⟩ := hd
    cases ds with
    | nil => exact absurd rfl hne
    | cons d l =>
      have := hall d (by simp)
      have hd45 : d ≠ 45 := by omega
      simp [tokPre, f42TokCode, hd45]
  · simp [tokPre, f42TokCode]

private theorem isTok_tokPre (ng : Bool) {ds : List ℕ} (hds : ∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57)
    (hd : ds ≠ []) : F42Tok (tokPre ng ds) := by
  cases ng
  · exact Or.inl ⟨by simpa [tokPre] using hd, by simpa [tokPre] using hds⟩
  · exact Or.inr ⟨ds, ⟨hd, hds⟩, by simp [tokPre]⟩

private theorem endTok (ng : Bool) (ds : List ℕ) (hds : ∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57)
    (hst : ¬ (ds = [] ∧ ng = true)) (R : List (List ℕ)) :
    (((tokPre ng ds :: R).filter (· != [])).map f42TokCode =
      (if ds = [] then [] else [intsK.codeOf (intsSt ng ds)]) ++
        (R.filter (· != [])).map f42TokCode) ∧
    (∀ l ∈ (tokPre ng ds :: R).filter (· != []), l ∈ R.filter (· != []) ∨ F42Tok l) := by
  by_cases hd : ds = []
  · have hng : ng = false := by
      cases ng
      · rfl
      · exact absurd ⟨hd, rfl⟩ hst
    subst hd
    subst hng
    have : tokPre false [] = [] := by simp [tokPre]
    refine ⟨by simp [this], fun l hl => Or.inl ?_⟩
    simpa [this] using hl
  · have hne : tokPre ng ds ≠ [] := by cases ng <;> simp [tokPre, hd]
    have hbne : (tokPre ng ds != []) = true := by simpa using hne
    have hdig : IsDigits ds := ⟨hd, hds⟩
    have htok : intsK.codeOf (intsSt ng ds) = f42TokCode (tokPre ng ds) := by
      rw [codeOf_intsSt ng hd, f42TokCode_tokPre ng hdig]
    constructor
    · rw [List.filter_cons, if_pos hbne, List.map_cons, if_neg hd, htok]
      rfl
    · intro l hl
      rw [List.filter_cons, if_pos hbne] at hl
      rcases List.mem_cons.1 hl with rfl | hl'
      · exact Or.inr (isTok_tokPre ng hds hd)
      · exact Or.inl hl'

private theorem two_le_intsSt (ng : Bool) (ds : List ℕ) : (2 ≤ intsSt ng ds) ↔ ds ≠ [] := by
  by_cases hd : ds = []
  · subst hd
    rw [intsSt_nil]
    cases ng <;> simp
  · rw [intsSt_ne hd]
    simp only [ne_eq, hd, not_false_eq_true, iff_true]
    omega

private theorem intsRun_nil_intsSt (ng : Bool) (ds : List ℕ) :
    intsRun [] (intsSt ng ds) = if ds = [] then [] else [intsK.codeOf (intsSt ng ds)] := by
  rw [intsRun_nil]
  by_cases hd : ds = []
  · have : ¬ 2 ≤ intsSt ng ds := fun h => (two_le_intsSt ng ds).1 h hd
    rw [if_neg this, if_pos hd]
  · have : 2 ≤ intsSt ng ds := (two_le_intsSt ng ds).2 hd
    rw [if_pos this, if_neg hd]

private theorem fmtRun_nil_iff' (st : ℕ) : fmtRun [] st = true ↔ st ≠ 1 := by
  rw [fmtRun_nil]
  constructor
  · intro h e
    subst e
    simp at h
  · intro h
    rw [beq_false_of_ne' h]
    rfl

private theorem fmtRun_nil_iff (ng : Bool) (ds : List ℕ) :
    fmtRun [] (fmtSt ng ds) = true ↔ ¬ (ds = [] ∧ ng = true) := by
  rw [fmtRun_nil_iff']
  by_cases hd : ds = []
  · subst hd
    cases ng <;> simp [fmtSt]
  · simp [fmtSt, hd]

private theorem tokPre_false_nil : tokPre false [] = [] := by simp [tokPre]

private theorem tokPre_true_nil : tokPre true [] = [45] := by simp [tokPre]

private theorem intsRun_main (cs : List ℕ) : ∀ (ng : Bool) (ds : List ℕ),
    (∀ c ∈ ds, 48 ≤ c ∧ c ≤ 57) → fmtRun cs (fmtSt ng ds) = true →
    intsRun cs (intsSt ng ds) =
        (((tokPre ng ds ++ cs).splitOnP f42Sep).filter (· != [])).map f42TokCode ∧
      (∀ l ∈ ((tokPre ng ds ++ cs).splitOnP f42Sep).filter (· != []), F42Tok l) := by
  induction cs with
  | nil =>
    intro ng ds hds h
    have hst := (fmtRun_nil_iff ng ds).1 h
    rw [List.append_nil, List.splitOnP_eq_singleton (tokPre_nosep ng hds)]
    obtain ⟨e1, e2⟩ := endTok ng ds hds hst []
    refine ⟨?_, fun l hl => ?_⟩
    · rw [intsRun_nil_intsSt]
      simpa using e1.symm
    · rcases e2 l hl with h | h
      · simp at h
      · exact h
  | cons c cs ih =>
    intro ng ds hds h
    by_cases hsep : c = 32 ∨ c = 10
    · rw [fmtRun_sep hsep] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hst1, h'⟩ := h
      have hst : ¬ (ds = [] ∧ ng = true) := by
        rintro ⟨rfl, rfl⟩
        simp [fmtSt] at hst1
      obtain ⟨ih1, ih2⟩ := ih false [] (by simp) (by simpa [fmtSt] using h')
      simp only [tokPre_false_nil, intsSt_nil, List.nil_append, Bool.false_eq_true,
        if_false] at ih1 ih2
      have hf : f42Sep c = true := by rcases hsep with rfl | rfl <;> rfl
      obtain ⟨e1, e2⟩ := endTok ng ds hds hst (cs.splitOnP f42Sep)
      rw [List.splitOnP_append_cons_of_forall_mem (tokPre_nosep ng hds) c hf]
      refine ⟨?_, fun l hl => ?_⟩
      · have : (if 2 ≤ intsSt ng ds then [intsK.codeOf (intsSt ng ds)] else []) =
            (if ds = [] then [] else [intsK.codeOf (intsSt ng ds)]) := by
          by_cases hd : ds = []
          · rw [if_neg (fun h => (two_le_intsSt ng ds).1 h hd), if_pos hd]
          · rw [if_pos ((two_le_intsSt ng ds).2 hd), if_neg hd]
        rw [intsRun_sep hsep, this, e1, ih1]
      · rcases e2 l hl with h2 | h2
        · exact ih2 l h2
        · exact h2
    · by_cases hdig : 48 ≤ c ∧ c ≤ 57
      · rw [fmtRun_digit hdig] at h
        have hds' : ∀ x ∈ ds ++ [c], 48 ≤ x ∧ x ≤ 57 := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hds x hx
          · simp at hx
            subst hx
            exact hdig
        have hne : ds ++ [c] ≠ [] := by simp
        obtain ⟨ih1, ih2⟩ := ih ng (ds ++ [c]) hds' (by rw [fmtSt_ne hne]; exact h)
        rw [tokPre_snoc] at ih1 ih2
        refine ⟨?_, ih2⟩
        rw [intsRun_digit hdig, intsSt_digit ng ds hdig]
        exact ih1
      · by_cases h45 : c = 45
        · subst h45
          rw [fmtRun_minus] at h
          simp only [Bool.and_eq_true, Nat.beq_eq] at h
          obtain ⟨hst0, h'⟩ := h
          have hdsnil : ds = [] ∧ ng = false := by
            by_cases hd : ds = []
            · subst hd
              cases ng
              · exact ⟨rfl, rfl⟩
              · simp [fmtSt] at hst0
            · simp [fmtSt, hd] at hst0
          obtain ⟨rfl, rfl⟩ := hdsnil
          obtain ⟨ih1, ih2⟩ := ih true [] (by simp) (by simpa [fmtSt] using h')
          simp only [tokPre_true_nil, tokPre_false_nil, intsSt_nil, List.nil_append,
            List.singleton_append, if_true] at ih1 ih2 ⊢
          refine ⟨?_, ih2⟩
          rw [intsRun_other (by omega) (by omega) (by omega)]
          exact ih1
        · exfalso
          rw [fmtRun_other (fun h32 => hsep (Or.inl h32)) (fun h10 => hsep (Or.inr h10))
            hdig h45] at h
          exact absurd h (by simp)

private theorem filterMap_toInt (L : List (List ℕ)) (hL : ∀ t ∈ L, t = [] ∨ F42Tok t) :
    L.filterMap (fun t => (strL t).toInt?) =
      ((L.filter fun t => t != []).map f42TokCode).map refOfCode := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have ih' := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    rcases hL t List.mem_cons_self with h0 | hT
    · subst h0
      rw [List.filterMap_cons, toInt?_strL_nil, List.filter_cons]
      simpa using ih'
    · have hne : t ≠ [] := by
        rcases hT with ⟨hne, -⟩ | ⟨ds, -, rfl⟩
        · exact hne
        · simp
      have hb : (t != []) = true := by simpa using hne
      rw [List.filterMap_cons, toInt?_f42Tok hT, List.filter_cons, if_pos hb]
      simp [ih']

end F42Parse

theorem fmtK_tok {cs : List ℕ} (h : fmtK cs = true) :
    ∀ t ∈ cs.splitOnP f42Sep, t = [] ∨ F42Tok t := by
  rw [fmtK_eq_run] at h
  obtain ⟨-, h2⟩ := intsRun_main cs false [] (by simp) (by simpa [fmtSt] using h)
  simp only [tokPre_false_nil, List.nil_append] at h2
  intro t ht
  by_cases h0 : t = []
  · exact Or.inl h0
  · exact Or.inr (h2 t (List.mem_filter.2 ⟨ht, by simpa using h0⟩))

theorem intsK_toks {cs : List ℕ} (h : fmtK cs = true) :
    intsK cs = (f42Toks cs).map f42TokCode := by
  rw [fmtK_eq_run] at h
  obtain ⟨h1, -⟩ := intsRun_main cs false [] (by simp) (by simpa [fmtSt] using h)
  simp only [tokPre_false_nil, intsSt_nil, List.nil_append, Bool.false_eq_true, if_false] at h1
  rw [intsK_eq_run]
  exact h1

theorem parseInts_strL_eq_intsK {cs : List ℕ} (h : fmtK cs = true) :
    parseInts (strL cs) = (intsK cs).map refOfCode := by
  rw [parseInts_strL, intsK_toks h]
  exact filterMap_toInt _ (fmtK_tok h)

end CFSG.KS.PK

end
