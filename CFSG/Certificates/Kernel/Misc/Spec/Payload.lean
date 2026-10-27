module

public import Certificates.Data.Kernel.Misc.G23
public import CFSG.Certificates.Kernel.Misc.Spec.ArrF2
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.Spec

open CFSG.KC.Misc.G23 (wsK afterNL entryK blowBits decodeK)
open CFSG.Sporadic.He.Native (decodeEntries rowsOf wsChar)

theorem wsK_iff (c : ℕ) :
    wsK c = true ↔ c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 11 ∨ c = 12 := by
  simp only [wsK, CFSG.KS.PK.orB_eq, Bool.or_eq_true, Nat.beq_eq]

theorem entryK_eq (c : ℕ) : entryK c = if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0 := by
  unfold entryK
  have : CFSG.KC.Ord.andB (Nat.ble 48 c) (Nat.ble c 57) = decide (48 ≤ c ∧ c ≤ 57) := by
    rw [Bool.eq_iff_iff]
    simp [CFSG.KS.PK.andB_eq, Nat.ble_eq]
  rw [this]
  by_cases h : 48 ≤ c ∧ c ≤ 57
  · rw [decide_eq_true h, if_pos h]
    rfl
  · rw [decide_eq_false h, if_neg h]

theorem afterNL_eq (cs : List ℕ) : afterNL cs = (cs.dropWhile fun c => c != 10).drop 1 := by
  induction cs with
  | nil => rfl
  | cons c t ih =>
    show Bool.rec (motive := fun _ => List ℕ) (afterNL t) t (Nat.beq c 10) = _
    by_cases h : c = 10
    · subst h
      simp
    · have hb : Nat.beq c 10 = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
      rw [hb]
      simp [List.dropWhile_cons, h, ih]

@[expose] def payloadEntries (cs : List ℕ) : List ℕ :=
  (((cs.dropWhile fun c => c != 10).drop 1).filter fun c =>
      !(c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12)).map fun c =>
    if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0

theorem ofNat_toNat_cases (c : ℕ) :
    ((Char.ofNat c).toNat = c ∨ (Char.ofNat c).toNat = 0) ∧
      (c < 128 → (Char.ofNat c).toNat = c) := by
  unfold Char.ofNat
  split
  · exact ⟨Or.inl rfl, fun _ => rfl⟩
  · rename_i h
    exact ⟨Or.inr rfl, fun hc => absurd (Or.inl (by omega)) h⟩

theorem ofNat_eq_char {c : ℕ} {d : Char} (hd : 0 < d.toNat) (hd' : d.toNat < 128) :
    Char.ofNat c = d ↔ c = d.toNat := by
  rw [← Char.toNat_inj]
  obtain ⟨h1, h2⟩ := ofNat_toNat_cases c
  constructor
  · intro h
    omega
  · intro h
    rw [h, Char.ofNat_toNat]

theorem ne_nl_ofNat (c : ℕ) : (Char.ofNat c != '\n') = (c != 10) := by
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq]
  rw [ofNat_eq_char (d := '\n') (by decide) (by decide)]
  rfl

theorem wsChar_ofNat (c : ℕ) :
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

theorem digit_ofNat (c : ℕ) :
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

theorem decodeEntries_ofList (cs : List ℕ) :
    decodeEntries (String.ofList (cs.map Char.ofNat)) = payloadEntries cs := by
  unfold decodeEntries payloadEntries
  have h1 : (String.ofList (cs.map Char.ofNat)).toList = cs.map Char.ofNat := by simp
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

@[expose] noncomputable def decR (l : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun c _ ih i acc => Bool.rec (motive := fun _ => ℕ)
      (ih (Nat.succ i) (Bool.rec (motive := fun _ => ℕ) acc
        (Nat.lor acc (blowBits i (Nat.mod (entryK c) 4))) (Nat.blt i 729)))
      (ih i acc) (wsK c)) l

theorem decodeK_eq_decR (cs : List ℕ) : decodeK cs = decR (afterNL cs) 0 0 := rfl

@[expose] noncomputable def entStep (i acc e : ℕ) : ℕ :=
  if i < 729 then acc ||| blowBits i e else acc

theorem decR_cons (c : ℕ) (l : List ℕ) (i acc : ℕ) :
    decR (c :: l) i acc = Bool.rec (motive := fun _ => ℕ)
      (decR l (Nat.succ i) (Bool.rec (motive := fun _ => ℕ) acc
        (Nat.lor acc (blowBits i (Nat.mod (entryK c) 4))) (Nat.blt i 729)))
      (decR l i acc) (wsK c) := rfl

theorem decR_ws {c : ℕ} (h : wsK c = true) (l : List ℕ) (i acc : ℕ) :
    decR (c :: l) i acc = decR l i acc := by
  rw [decR_cons, h]

theorem decR_ent {c : ℕ} (h : wsK c = false) (l : List ℕ) (i acc : ℕ) :
    decR (c :: l) i acc = decR l (i + 1) (entStep i acc (entryK c % 4)) := by
  rw [decR_cons, h]
  show decR l (Nat.succ i) _ = _
  congr 1
  unfold entStep
  by_cases hi : i < 729
  · have : Nat.blt i 729 = true := Nat.blt_eq.mpr hi
    rw [this, if_pos hi]
    rfl
  · have : Nat.blt i 729 = false := by
      rw [Bool.eq_false_iff]
      intro h'
      exact hi (Nat.blt_eq.mp h')
    rw [this, if_neg hi]

noncomputable def entFold : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | e :: t, i, acc => entFold t (i + 1) (entStep i acc (e % 4))

theorem decR_eq_entFold (l : List ℕ) :
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

theorem testBit_entStep (i acc e q : ℕ) :
    (entStep i acc e).testBit q = (acc.testBit q || (decide (i < 729) &&
      (blowBits i e).testBit q)) := by
  unfold entStep
  by_cases h : i < 729
  · rw [if_pos h, Nat.testBit_or]
    simp [h]
  · rw [if_neg h]
    simp [h]

theorem testBit_entFold (q : ℕ) : ∀ (G : List ℕ) (i acc : ℕ),
    (entFold G i acc).testBit q = true ↔ acc.testBit q = true ∨ ∃ s < G.length, i + s < 729 ∧
      (blowBits (i + s) (G.getD s 0 % 4)).testBit q = true := by
  intro G
  induction G with
  | nil =>
    intro i acc
    simp [entFold]
  | cons e t ih =>
    intro i acc
    rw [entFold, ih, testBit_entStep]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h | ⟨hi, h⟩) | ⟨s, hs, hi, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, by simp, by simpa using hi, by simpa using h⟩
      · refine Or.inr ⟨s + 1, by simpa using hs, ?_, ?_⟩
        · omega
        · rw [show i + (s + 1) = i + 1 + s by omega]
          simpa using h
    · rintro (h | ⟨s, hs, hi, h⟩)
      · exact Or.inl (Or.inl h)
      · cases s with
        | zero => exact Or.inl (Or.inr ⟨by simpa using hi, by simpa using h⟩)
        | succ s =>
          refine Or.inr ⟨s, by simpa using hs, by omega, ?_⟩
          rw [show i + 1 + s = i + (s + 1) by omega]
          simpa using h

theorem entries_eq (cs : List ℕ) :
    ((afterNL cs).filter fun c => !wsK c).map entryK = payloadEntries cs := by
  rw [afterNL_eq]
  unfold payloadEntries
  have e1 : (fun c : ℕ => !wsK c) =
      fun c => !(c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12) := by
    funext c
    have : wsK c = (c == 32 || c == 9 || c == 10 || c == 13 || c == 11 || c == 12) := by
      rw [Bool.eq_iff_iff, wsK_iff]
      simp only [Bool.or_eq_true, beq_iff_eq]
      tauto
    rw [this]
  have e2 : entryK = fun c : ℕ => if 48 ≤ c ∧ c ≤ 57 then c - 48 else 0 := by
    funext c
    exact entryK_eq c
  rw [e1, e2]

theorem testBit_decodeK (cs : List ℕ) (q : ℕ) :
    (decodeK cs).testBit q = true ↔ ∃ s < (payloadEntries cs).length, s < 729 ∧
      (blowBits s ((payloadEntries cs).getD s 0 % 4)).testBit q = true := by
  rw [decodeK_eq_decR, decR_eq_entFold, entries_eq, testBit_entFold]
  simp

theorem blowBits_eq (i e : ℕ) :
    blowBits i e = blkBits 54 (2 * 54 * (i / 27) + 2 * (i % 27)) e := by
  unfold blowBits
  simp only [CFSG.KS.PK.letN_eq]
  rfl

theorem blk_zero_digit (a b : ℕ) : blk 0 a b = 0 := by
  unfold blk
  split_ifs <;> simp

theorem pkMat_decodeK (cs : List ℕ) :
    pkMat 54 (decodeK cs) =
      toM (CFSG.LieType.Multipliers.G23.blowUp
        (rowsOf 4 27 (String.ofList (cs.map Char.ofNat)))) := by
  ext R C
  have hR := R.isLt
  have hC := C.isLt
  have hi : R.val / 2 < 27 := by omega
  have hk : C.val / 2 < 27 := by omega
  set G := payloadEntries cs with hG
  set k0 := 27 * (R.val / 2) + C.val / 2 with hk0
  have hbit : (decodeK cs).testBit (54 * R.val + C.val) = true ↔
      blk (G.getD k0 0 % 4) (R.val % 2) (C.val % 2) = 1 := by
    rw [testBit_decodeK]
    constructor
    · rintro ⟨s, hs, hs729, h⟩
      rw [blowBits_eq] at h
      obtain ⟨h1, h2, h3⟩ :=
        (testBit_blkBits (N := 54) (i := s / 27) (j := s % 27) (by omega) hC).1 h
      have e : s = k0 := by omega
      rw [← e]
      exact h3
    · intro h
      have hlen : k0 < G.length := by
        by_contra hcon
        have h0 : G.getD k0 0 = 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : G.length ≤ k0)]
        rw [h0, Nat.zero_mod, blk_zero_digit] at h
        exact absurd h (by norm_num)
      refine ⟨k0, hlen, by omega, ?_⟩
      rw [blowBits_eq]
      exact (testBit_blkBits (N := 54) (i := k0 / 27) (j := k0 % 27) (by omega) hC).2
        ⟨by omega, by omega, h⟩
  have hrows : ((rowsOf 4 27 (String.ofList (cs.map Char.ofNat)))[R.val / 2]!)[C.val / 2]! =
      G.getD k0 0 % 4 := by
    unfold rowsOf
    rw [ofFn_getElem! _ hi, ofFn_getElem! _ hk]
    simp only [List.getElem?_toArray, decodeEntries_ofList]
    rw [← hG, List.getD_eq_getElem?_getD, hk0, Nat.mul_comm]
  have hentry : toM (CFSG.LieType.Multipliers.G23.blowUp
      (rowsOf 4 27 (String.ofList (cs.map Char.ofNat)))) R C =
      ((blk (G.getD k0 0 % 4) (R.val % 2) (C.val % 2) : ℕ) : ZMod 2) := by
    show ((((CFSG.LieType.Multipliers.G23.blowUp
      (rowsOf 4 27 (String.ofList (cs.map Char.ofNat))))[R.val]!)[C.val]! : ℕ) : ZMod 2) = _
    rw [blowUp_entry, hrows]
    rfl
  rw [hentry]
  have hlt := blk_lt (G.getD k0 0 % 4) (R.val % 2) (C.val % 2)
  show (if (decodeK cs).testBit (54 * R.val + C.val) = true then (1 : ZMod 2) else 0) = _
  by_cases hb : (decodeK cs).testBit (54 * R.val + C.val) = true
  · rw [if_pos hb, hbit.1 hb]
    simp
  · have hb1 : ¬ blk (G.getD k0 0 % 4) (R.val % 2) (C.val % 2) = 1 := fun e => hb (hbit.2 e)
    have hb0 : blk (G.getD k0 0 % 4) (R.val % 2) (C.val % 2) = 0 := by omega
    rw [if_neg hb, hb0]
    simp

end CFSG.KC.Misc.Spec

end
