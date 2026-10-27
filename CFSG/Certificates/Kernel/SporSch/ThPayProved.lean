
module

public import CFSG.Certificates.Kernel.SporSch.ThRowsProved

public section

namespace CFSG.KS.SporSch.Pf

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th

@[expose] def valC (c : Char) : Nat := if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

@[expose] def ents (D : List Char) : List Nat := (D.filter fun c => !wsChar c).map valC

@[expose] def ent (l : List Nat) (k : Nat) : Bool := l.getD k 0 % 2 == 1

theorem chb (ch d : Char) : (ch == d) = Nat.beq ch.toNat d.toNat := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq]
  constructor
  · rintro rfl
    exact Nat.beq_refl _
  · intro h
    exact Char.toNat_inj.1 (Nat.eq_of_beq_eq_true h)

theorem nb (a b : Nat) : (a == b) = Nat.beq a b := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq]
  exact ⟨fun h => h ▸ Nat.beq_refl a, Nat.eq_of_beq_eq_true⟩

theorem wsT_eq (ch : Char) : wsT ch.toNat = wsChar ch := by
  unfold wsChar
  rw [chb, chb, chb, chb, nb, nb]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  unfold wsT
  cases Nat.beq ch.toNat 32 <;> cases Nat.beq ch.toNat 9 <;> cases Nat.beq ch.toNat 10 <;>
    cases Nat.beq ch.toNat 13 <;> cases Nat.beq ch.toNat 11 <;> cases Nat.beq ch.toNat 12 <;> rfl

theorem digit_iff (ch : Char) :
    (('0' ≤ ch && ch ≤ '9') = true) ↔ (48 ≤ ch.toNat ∧ ch.toNat ≤ 57) := by
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact Iff.and UInt32.le_iff_toNat_le UInt32.le_iff_toNat_le

theorem parT_eq (ch : Char) : parT ch.toNat = valC ch % 2 := by
  unfold parT valC
  by_cases hd : ('0' ≤ ch && ch ≤ '9') = true
  · rw [ite_eq_left hd]
    obtain ⟨h1, h2⟩ := (digit_iff ch).1 hd
    rw [Nat.ble_eq_true_of_le h1, Nat.ble_eq_true_of_le h2]
    exact Nat.and_one_is_mod _
  · rw [ite_eq_right hd]
    have hn : ¬ (48 ≤ ch.toNat ∧ ch.toNat ≤ 57) := fun h => hd ((digit_iff ch).2 h)
    cases h1 : Nat.ble 48 ch.toNat
    · rfl
    · cases h2 : Nat.ble ch.toNat 57
      · rfl
      · exact absurd ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩ hn

theorem parT_lt (ch : Char) : parT ch.toNat < 2 := by
  rw [parT_eq]
  exact Nat.mod_lt _ (by decide)

theorem testBit_par (ch : Char) (j c : Nat) :
    (Nat.shiftLeft (parT ch.toNat) j).testBit c = (decide (c = j) && (valC ch % 2 == 1)) := by
  change ((parT ch.toNat) <<< j).testBit c = _
  rw [Nat.testBit_shiftLeft, parT_eq]
  by_cases hcj : c = j
  · subst hcj
    rcases Nat.mod_two_eq_zero_or_one (valC ch) with h | h <;> simp [h]
  · by_cases hlt : j ≤ c
    · have hpos : 0 < c - j := by omega
      have hlt2 := Nat.mod_lt (valC ch) (by decide : 0 < 2)
      have : (valC ch % 2).testBit (c - j) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt2 (by
          have : 2 ^ 1 ≤ 2 ^ (c - j) := Nat.pow_le_pow_right (by decide) hpos
          simpa using this))
      simp [hcj, hlt, this]
    · simp [hcj, hlt]

@[expose] def RowsAt (R : Nat → Nat) (i j acc : Nat) (l : List Nat) : Prop :=
  ∀ r, i ≤ r → r < 248 → R r < 2 ^ 248 ∧ ∀ c < 248, (R r).testBit c =
    if r * 248 + c < i * 248 + j then acc.testBit c else ent l (r * 248 + c - (i * 248 + j))

theorem allBlk_spec' {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, allBlk b f len = true → ∀ l < len, f (Nat.add b l) = true :=
  CFSG.KC.Pack.allBlk_spec

theorem thPayRun_nil (R : Nat → Nat) (ph i j acc : Nat) : thPayRun R [] ph i j acc =
    Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool) false
        (allBlk (Nat.succ i) (fun r => Nat.beq (R r) 0) (Nat.sub 247 i)) (Nat.beq (R i) acc))
      (Nat.blt i 248) := rfl

theorem thPayRun_cons (R : Nat → Nat) (ch : Char) (cs : List Char) (ph i j acc : Nat) :
    thPayRun R (ch :: cs) ph i j acc =
    strictB (Char.toNat ch) (fun c =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) (thPayRun R cs 1 i j acc)
            (strictB (Nat.lor acc (Nat.shiftLeft (parT c) j)) (fun acc' =>
              Bool.rec (motive := fun _ => Bool)
                (strictB (Nat.succ j) (fun j' => thPayRun R cs 1 i j' acc'))
                (Bool.rec (motive := fun _ => Bool) false
                  (strictB (Nat.succ i) (fun i' => thPayRun R cs 1 i' 0 0)) (Nat.beq (R i) acc'))
                (Nat.beq (Nat.succ j) 248)))
            (Nat.blt i 248))
          (thPayRun R cs 1 i j acc) (wsT c))
        (Bool.rec (motive := fun _ => Bool) (thPayRun R cs 0 i j acc) (thPayRun R cs 1 i j acc)
          (Nat.beq c 10))
        (Nat.beq ph 0)) := rfl

theorem strictB_e (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_e (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem band_t {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem end_rows (R : Nat → Nat) {i j acc : Nat} (hj : j < 248) (hacc : ∀ c, j ≤ c → acc.testBit c = false)
    (hlt : acc < 2 ^ 248) (h : thPayRun R [] 1 i j acc = true) : RowsAt R i j acc [] := by
  rw [thPayRun_nil] at h
  intro r hir hr
  have hi : i < 248 := by omega
  have hb : Nat.blt i 248 = true := Nat.blt_eq.mpr hi
  rw [hb] at h
  obtain ⟨h1, h2⟩ := band_t h
  have hRi : R i = acc := Nat.eq_of_beq_eq_true h1
  have hz : ∀ r, i < r → r < 248 → R r = 0 := by
    intro r h1' h2'
    have := allBlk_spec' h2 (r - i - 1) (by change r - i - 1 < 247 - i; omega)
    have e : Nat.add (Nat.succ i) (r - i - 1) = r := by change i + 1 + (r - i - 1) = r; omega
    rw [e] at this
    exact Nat.eq_of_beq_eq_true this
  have hent : ∀ k, ent [] k = false := fun k => by simp [ent]
  rcases Nat.lt_or_eq_of_le hir with h' | rfl
  · rw [hz r h' hr]
    refine ⟨Nat.two_pow_pos _, fun c hc => ?_⟩
    rw [Nat.zero_testBit, ite_eq_right (by omega), hent]
  · rw [hRi]
    refine ⟨hlt, fun c hc => ?_⟩
    by_cases hcj : c < j
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), hent, hacc c (by omega)]

theorem acc_bit (ch : Char) (acc j c : Nat) :
    (Nat.lor acc (Nat.shiftLeft (parT ch.toNat) j)).testBit c =
      (acc.testBit c || (decide (c = j) && (valC ch % 2 == 1))) := by
  change (acc ||| Nat.shiftLeft (parT ch.toNat) j).testBit c = _
  rw [Nat.testBit_or, testBit_par]

theorem acc_lt {ch : Char} {acc j : Nat} (hlt : acc < 2 ^ 248) (hj : j < 248) :
    Nat.lor acc (Nat.shiftLeft (parT ch.toNat) j) < 2 ^ 248 :=
  Nat.lt_pow_two_of_testBit _ fun c hc => by
    rw [acc_bit, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt
      (Nat.pow_le_pow_right (by decide) hc)), decide_eq_false (by omega)]
    rfl

theorem ent_cons (x : Nat) (l : List Nat) (k : Nat) : ent (x :: l) (k + 1) = ent l k := by
  simp [ent]

theorem ent_zero (x : Nat) (l : List Nat) : ent (x :: l) 0 = (x % 2 == 1) := by
  simp [ent]

theorem data_sound (R : Nat → Nat) : ∀ (cs : List Char) (i j acc : Nat), j < 248 →
    (∀ c, j ≤ c → acc.testBit c = false) → acc < 2 ^ 248 →
    thPayRun R cs 1 i j acc = true → RowsAt R i j acc (ents cs)
  | [], i, j, acc, hj, hacc, hlt, h => by
    have := end_rows R hj hacc hlt h
    simpa [ents] using this
  | ch :: cs, i, j, acc, hj, hacc, hlt, h => by
    rw [thPayRun_cons, strictB_e] at h
    have e10 : Nat.beq 1 0 = false := rfl
    rw [e10] at h
    cases hw : wsT ch.toNat
    · rw [hw] at h
      have hents : ents (ch :: cs) = valC ch :: ents cs := by
        rw [ents, ents, List.filter_cons, ← wsT_eq, hw]
        rfl
      rw [hents]
      cases hb : Nat.blt i 248
      · intro r hir hr
        have : ¬ i < 248 := fun hi => by rw [Nat.blt_eq.mpr hi] at hb; exact Bool.noConfusion hb
        omega
      · rw [hb] at h
        have hi : i < 248 := Nat.blt_eq.mp hb
        change strictB (Nat.lor acc (Nat.shiftLeft (parT ch.toNat) j)) _ = true at h
        rw [strictB_e] at h
        cases hj1 : Nat.beq (Nat.succ j) 248
        · rw [hj1] at h
          change strictB (Nat.succ j) _ = true at h
          rw [strictB_e] at h
          have hj1' : j + 1 ≠ 248 := Nat.ne_of_beq_eq_false hj1
          have ih := data_sound R cs i (j + 1) _ (by omega) (fun c hc => by
            rw [acc_bit, hacc c (by omega), decide_eq_false (by omega)]
            rfl) (acc_lt hlt hj) h
          intro r hir hr
          obtain ⟨hR1, hR2⟩ := ih r hir hr
          refine ⟨hR1, fun c hc => ?_⟩
          rw [hR2 c hc]
          by_cases h1 : r * 248 + c < i * 248 + j
          · have hri : r = i := by omega
            subst hri
            rw [ite_eq_left (by omega), ite_eq_left h1, acc_bit, decide_eq_false (by omega)]
            simp
          · rw [ite_eq_right h1]
            by_cases h2 : r * 248 + c = i * 248 + j
            · have hri : r = i := by omega
              subst hri
              have hcj : c = j := by omega
              subst hcj
              rw [ite_eq_left (by omega), acc_bit, hacc c le_rfl, h2, Nat.sub_self, ent_zero]
              simp
            · rw [ite_eq_right (by omega), show r * 248 + c - (i * 248 + j) =
                (r * 248 + c - (i * 248 + (j + 1))) + 1 by omega, ent_cons]
        · rw [hj1] at h
          have hj7 : j + 1 = 248 := Nat.eq_of_beq_eq_true hj1
          obtain ⟨h1, h2⟩ := band_t h
          rw [strictB_e] at h2
          have hRi : R i = Nat.lor acc (Nat.shiftLeft (parT ch.toNat) j) := Nat.eq_of_beq_eq_true h1
          have ih := data_sound R cs (i + 1) 0 0 (by omega) (fun c _ => Nat.zero_testBit c)
            (Nat.two_pow_pos _) h2
          intro r hir hr
          rcases Nat.lt_or_eq_of_le hir with h' | rfl
          · obtain ⟨hR1, hR2⟩ := ih r h' hr
            refine ⟨hR1, fun c hc => ?_⟩
            rw [hR2 c hc, ite_eq_right (by omega), ite_eq_right (by omega),
              show r * 248 + c - (i * 248 + j) = (r * 248 + c - ((i + 1) * 248 + 0)) + 1 by omega,
              ent_cons]
          · rw [hRi]
            refine ⟨acc_lt hlt hj, fun c hc => ?_⟩
            rw [acc_bit]
            by_cases hcj : c < j
            · rw [ite_eq_left (by omega), decide_eq_false (by omega)]
              simp
            · have hcj' : c = j := by omega
              subst hcj'
              rw [ite_eq_right (by omega), hacc c le_rfl, Nat.sub_self, ent_zero]
              simp
    · rw [hw] at h
      have hents : ents (ch :: cs) = ents cs := by
        rw [ents, ents, List.filter_cons, ← wsT_eq, hw]
        rfl
      rw [hents]
      exact data_sound R cs i j acc hj hacc hlt h

theorem nl_of (ch : Char) (h : Nat.beq ch.toNat 10 = true) : ch = '\n' :=
  Char.toNat_inj.1 (Nat.eq_of_beq_eq_true h)

theorem head_sound (R : Nat → Nat) : ∀ cs : List Char, thPayRun R cs 0 0 0 0 = true →
    RowsAt R 0 0 0 (ents ((cs.dropWhile (· != '\n')).drop 1))
  | [], h => by
    have h' : thPayRun R [] 1 0 0 0 = true := h
    simpa [ents] using end_rows R (by decide) (fun c _ => Nat.zero_testBit c) (Nat.two_pow_pos _) h'
  | ch :: cs, h => by
    rw [thPayRun_cons, strictB_e] at h
    have e00 : Nat.beq 0 0 = true := rfl
    rw [e00] at h
    cases h10 : Nat.beq ch.toNat 10
    · rw [h10] at h
      have hne : (ch != '\n') = true := by
        rw [bne_iff_ne]
        rintro rfl
        exact absurd h10 (by decide)
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') hne]
      exact head_sound R cs h
    · rw [h10] at h
      have hc := nl_of ch h10
      subst hc
      rw [List.dropWhile_cons_of_neg (p := fun x => x != '\n') (by decide), List.drop_one,
        List.tail_cons]
      exact data_sound R cs 0 0 0 (by decide) (fun c _ => Nat.zero_testBit c)
        (Nat.two_pow_pos _) h

end CFSG.KS.SporSch.Pf

end

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th
open CFSG.KS.SporSch.Pf

theorem thPay_sound_proved {R : Nat → Nat} {cs : List Char} (h : thPayK R cs = true) :
    rowsOf (String.ofList cs) = rowsV R := by
  have hR := head_sound R cs h
  have hdec : decodeEntries (String.ofList cs) = ents ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold decodeEntries
    rw [String.toList_ofList]
    rfl
  unfold rowsOf
  rw [hdec]
  apply Array.ext (by rw [Array.size_ofFn, rowsV_size])
  intro r h1 h2
  have hr : r < 248 := by rw [rowsV_size] at h2; exact h2
  rw [getElem_rowsV _ h2, Array.getElem_ofFn]
  obtain ⟨hlt, hbits⟩ := hR r (Nat.zero_le _) hr
  unfold rowOfEntries
  apply V4.eq_of_toVec_eq (V4.ofFn_wf _) (v4OfNat_wf hlt)
  funext c
  have hc : ¬ (r * 248 + c.val < 0 * 248 + 0) := by omega
  rw [V4.toVec_ofFn, toVec_v4OfNat, rowOfNat, hbits c.val c.isLt, ite_eq_right hc]
  simp [ent, List.getElem?_toArray, List.getD_eq_getElem?_getD]

end CFSG.KS.SporSch

end
