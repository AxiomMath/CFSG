module

public import Certificates.Data.Kernel.Spor.TextAt
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.Text

open CFSG.KC.Enum CFSG.KS CFSG.KS.PackFld

@[expose] noncomputable def hexNum (v : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun v c => v * 16 + hexV c.toNat) v

theorem strictB_eqT (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def lineStep (wd n w P : Nat) (ch : Char) (ih : Nat → Nat → Nat → Nat → Bool)
    (e t v acc : Nat) : Bool :=
  bIf(Nat.blt e n,
    strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
      bIf(Nat.beq (Nat.succ t) wd,
        bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
          strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
            ih (Nat.succ e) (nat_lit 0) (nat_lit 0) acc'),
          false),
        ih e (Nat.succ t) v' acc)),
      false)),
    Nat.beq acc P)

theorem lineRun_cons (wd n w P : Nat) (ch : Char) (ds : List Char) (e t v acc : Nat) :
    lineRun wd n w P (ch :: ds) e t v acc = lineStep wd n w P ch (lineRun wd n w P ds) e t v acc :=
  rfl

theorem bool_rec_true {α : Sort _} (a b : α) : Bool.rec (motive := fun _ => α) a b true = b := rfl

theorem bool_rec_false {α : Sort _} (a b : α) : Bool.rec (motive := fun _ => α) a b false = a := rfl

theorem bool_rec_eq {α : Sort _} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = if c = true then b else a := by
  cases c <;> rfl

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rwa [Nat.blt_eq]

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (lt_of_blt hb) h

theorem beq_false' {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem lineStep_eq (wd n w P : Nat) (ch : Char) (ih : Nat → Nat → Nat → Nat → Bool)
    (e t v acc : Nat) : lineStep wd n w P ch ih e t v acc =
      if e < n then
        (if hexV ch.toNat < 16 then
          (if t + 1 = wd then
            (if v * 16 + hexV ch.toNat < 2 ^ w then
              ih (e + 1) 0 0 (acc ||| (v * 16 + hexV ch.toNat) <<< (w * e)) else false)
          else ih e (t + 1) (v * 16 + hexV ch.toNat) acc)
        else false)
      else Nat.beq acc P := by
  have e2 : Nat.shiftLeft 1 w = 2 ^ w := by
    change 1 <<< w = 2 ^ w
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  unfold lineStep
  simp only [bool_rec_eq, strictB_eqT, Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq,
    Nat.succ_eq_add_one, e2]
  rfl

theorem lineRun_nil (wd n w P e t v acc : Nat) :
    lineRun wd n w P [] e t v acc = (Nat.beq e n && Nat.beq acc P) := by
  change Bool.rec (motive := fun _ => Bool) false (Nat.beq acc P) (Nat.beq e n) = _
  generalize Nat.beq e n = b
  cases b <;> rfl

theorem lineRun_entry {wd n w P : Nat} : ∀ (ds : List Char) (e t v acc : Nat), e < n → t < wd →
    lineRun wd n w P ds e t v acc = true →
    wd - t ≤ ds.length ∧ (∀ c ∈ ds.take (wd - t), hexV c.toNat < 16) ∧
      hexNum v (ds.take (wd - t)) < 2 ^ w ∧
      lineRun wd n w P (ds.drop (wd - t)) (e + 1) 0 0
        (acc ||| hexNum v (ds.take (wd - t)) <<< (w * e)) = true
  | [], e, t, v, acc, he, _, h => by
    rw [lineRun_nil, Bool.and_eq_true] at h
    exact absurd (Nat.eq_of_beq_eq_true h.1) (by omega)
  | ch :: ds, e, t, v, acc, he, ht, h => by
    rw [lineRun_cons, lineStep_eq, ite_eq_left he] at h
    by_cases h2 : hexV ch.toNat < 16
    · rw [ite_eq_left h2] at h
      by_cases h3 : t + 1 = wd
      · rw [ite_eq_left h3] at h
        by_cases h4 : v * 16 + hexV ch.toNat < 2 ^ w
        · rw [ite_eq_left h4] at h
          have e1 : wd - t = 1 := by omega
          rw [e1]
          refine ⟨by simp, fun c hc => ?_, h4, h⟩
          simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
            or_false] at hc
          subst hc
          exact h2
        · rw [ite_eq_right h4] at h
          exact absurd h Bool.false_ne_true
      · rw [ite_eq_right h3] at h
        obtain ⟨h1', h2', h3', h4'⟩ := lineRun_entry ds e (t + 1) _ acc he (by omega) h
        have e1 : wd - t = (wd - (t + 1)) + 1 := by omega
        rw [e1, List.take_succ_cons, List.drop_succ_cons]
        refine ⟨by simp; omega, fun c hc => ?_, h3', h4'⟩
        rcases List.mem_cons.1 hc with rfl | hc
        · exact h2
        · exact h2' c hc
    · rw [ite_eq_right h2] at h
      exact absurd h Bool.false_ne_true

theorem lineRun_all {wd n w P : Nat} (hwd : 0 < wd) : ∀ (k : Nat) (ds : List Char) (e acc : Nat) (a : Nat → Nat),
    e + k = n → (∀ i < e, a i < 2 ^ w) → Fld w acc (fun i => if i < e then a i else 0) →
    lineRun wd n w P ds e 0 0 acc = true →
    (∀ i, e ≤ i → i < n → (i - e) * wd + wd ≤ ds.length ∧
      (∀ c ∈ (ds.drop ((i - e) * wd)).take wd, hexV c.toNat < 16) ∧
      pg w (mask w) P i = hexNum 0 ((ds.drop ((i - e) * wd)).take wd)) ∧
    ∀ i < e, pg w (mask w) P i = a i
  | 0, ds, e, acc, a, hk, ha, hacc, h => by
    have hP : acc = P := by
      cases ds with
      | nil =>
        rw [lineRun_nil, Bool.and_eq_true] at h
        exact Nat.eq_of_beq_eq_true h.2
      | cons ch ds =>
        rw [lineRun_cons, lineStep_eq, ite_eq_right (by omega)] at h
        exact Nat.eq_of_beq_eq_true h
    subst hP
    refine ⟨fun i h1 h2 => absurd h2 (by omega), fun i hi => ?_⟩
    have hg : (if i < e then a i else 0) < 2 ^ w := by
      rw [ite_eq_left hi]
      exact ha i hi
    have := pg_of_fld (i := i) hacc hg
    rw [this, ite_eq_left hi]
  | k + 1, ds, e, acc, a, hk, ha, hacc, h => by
    obtain ⟨h1, h2, h3, h4⟩ := lineRun_entry ds e 0 0 acc (by omega) hwd h
    rw [Nat.sub_zero] at h1 h2 h3 h4
    generalize hv : hexNum 0 (ds.take wd) = v at h3 h4
    let a' : Nat → Nat := fun i => if i = e then v else a i
    have hacc' : Fld w (acc ||| v <<< (w * e)) (fun i => if i < e + 1 then a' i else 0) := by
      refine fld_congr (fld_or hacc (fld_shl e (fld_one h3))) fun i => ?_
      by_cases hi : i < e
      · have hie : ¬ e ≤ i := by omega
        have hie' : i ≠ e := by omega
        simp [hi, hie, hie', a', show i < e + 1 by omega]
      · by_cases hie : i = e
        · subst hie
          simp [a']
        · have hi1 : ¬ i < e + 1 := by omega
          have hie2 : i - e ≠ 0 := by omega
          simp [hi, hi1, hie2, show e ≤ i by omega]
    have ha' : ∀ i < e + 1, a' i < 2 ^ w := by
      intro i hi
      by_cases hie : i = e
      · simp only [a', hie, ↓reduceIte]
        exact h3
      · simp only [a', hie, ↓reduceIte]
        exact ha i (by omega)
    obtain ⟨g1, g2⟩ := lineRun_all hwd k (ds.drop wd) (e + 1) _ a' (by omega) ha' hacc' h4
    refine ⟨fun i hi1 hi2 => ?_, fun i hi => ?_⟩
    · by_cases hie : i = e
      · subst hie
        rw [Nat.sub_self, Nat.zero_mul, List.drop_zero]
        refine ⟨by omega, h2, ?_⟩
        rw [g2 i (by omega)]
        change (if i = i then v else a i) = _
        rw [ite_eq_left rfl, hv]
      · obtain ⟨f1, f2, f3⟩ := g1 i (by omega) hi2
        have e1 : (i - e) * wd = wd + (i - (e + 1)) * wd := by
          rw [show i - e = (i - (e + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [List.drop_drop, ← e1] at f2 f3
        refine ⟨?_, f2, f3⟩
        rw [List.length_drop] at f1
        rw [e1]
        omega
    · rw [g2 i (by omega)]
      simp [a', show i ≠ e by omega]

theorem asciiK_spec : ∀ {cs : List Char}, asciiK cs = true → ∀ c ∈ cs, c.toNat < 128
  | [], _, c, hc => by cases hc
  | ch :: cs, h, c, hc => by
    have h' : (Nat.blt ch.toNat 128 && asciiK cs) = true := by
      change Bool.rec (motive := fun _ => Bool) false (asciiK cs) (Nat.blt (Char.toNat ch) 128) = true at h
      cases hb : Nat.blt (Char.toNat ch) 128 <;> rw [hb] at h
      · exact absurd h Bool.false_ne_true
      · rw [Bool.true_and]
        exact h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hc with rfl | hc
    · exact lt_of_blt h'.1
    · exact asciiK_spec h'.2 c hc

theorem asciiK_of : ∀ {cs : List Char}, (∀ c ∈ cs, c.toNat < 128) → asciiK cs = true
  | [], _ => rfl
  | ch :: cs, h => by
    change Bool.rec (motive := fun _ => Bool) false (asciiK cs) (Nat.blt (Char.toNat ch) 128) = true
    rw [blt_true (h ch List.mem_cons_self)]
    exact asciiK_of fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem utf8_char {c : Char} (h : c.toNat < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  have h' : c.val.toNat ≤ 0x7f := by
    have : c.toNat = c.val.toNat := rfl
    omega
  simp only [String.utf8EncodeChar, h', ↓reduceIte]
  rfl

theorem flatMap_ascii' : ∀ (l : List Char), (∀ c ∈ l, c.toNat < 128) →
    l.flatMap String.utf8EncodeChar = l.map fun c => UInt8.ofNat c.toNat
  | [], _ => rfl
  | c :: l, h => by
    rw [List.flatMap_cons, utf8_char (h c List.mem_cons_self),
      flatMap_ascii' l (fun c' hc => h c' (List.mem_cons_of_mem _ hc)), List.map_cons]
    rfl

theorem byteArray_get!_eq (b : ByteArray) (j : Nat) : b.get! j = b.data[j]! := by
  cases b
  rfl

theorem get!_toUTF8 {cs : List Char} {K j : Nat} (ha : ∀ c ∈ cs.take K, c.toNat < 128)
    (hj : j < K) (hl : j < cs.length) :
    (String.ofList cs).toUTF8.get! j = UInt8.ofNat (cs[j]'hl).toNat := by
  have e : cs.flatMap String.utf8EncodeChar =
      (cs.take K).map (fun c => UInt8.ofNat c.toNat) ++ (cs.drop K).flatMap String.utf8EncodeChar := by
    conv => lhs; rw [← List.take_append_drop K cs]
    rw [List.flatMap_append, flatMap_ascii' _ ha]
  have hjt : j < ((cs.take K).map (fun c => UInt8.ofNat c.toNat)).length := by simp; omega
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode, e,
    byteArray_get!_eq, List.data_toByteArray, getElem!_pos _ j (by simp at hjt ⊢; omega),
    List.getElem_toArray, List.getElem_append_left hjt, List.getElem_map, List.getElem_take]

theorem hexV_eq (c : Nat) : hexV c =
    if c < 48 then 16 else if c < 58 then c - 48 else if c < 65 then 16 else if c < 71 then c - 55
    else 16 := by
  unfold hexV
  by_cases h1 : c < 48
  · rw [blt_true h1, ite_eq_left h1]
  · rw [blt_false h1, ite_eq_right h1]
    by_cases h2 : c < 58
    · rw [blt_true h2, ite_eq_left h2]
      rfl
    · rw [blt_false h2, ite_eq_right h2]
      by_cases h3 : c < 65
      · rw [blt_true h3, ite_eq_left h3]
      · rw [blt_false h3, ite_eq_right h3]
        by_cases h4 : c < 71
        · rw [blt_true h4, ite_eq_left h4]
          rfl
        · rw [blt_false h4, ite_eq_right h4]

theorem hexVal_eq {c : Nat} (h : hexV c < 16) :
    CFSG.Monster.B.Max2.Native.hexVal (UInt8.ofNat c) = hexV c := by
  rw [hexV_eq] at h ⊢
  have e : c < 256 → (UInt8.ofNat c).toNat = c := fun hc => by
    exact UInt8.toNat_ofNat_of_lt' hc
  unfold CFSG.Monster.B.Max2.Native.hexVal
  by_cases h1 : c < 48
  · rw [ite_eq_left h1] at h
    omega
  · by_cases h2 : c < 58
    · rw [ite_eq_right h1, ite_eq_left h2, e (by omega), ite_eq_left h2]
    · by_cases h3 : c < 65
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] at h
        omega
      · by_cases h4 : c < 71
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4, e (by omega),
            ite_eq_right h2]
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4] at h
          omega

theorem hexAt_seg {b : ByteArray} {o : Nat} {seg : List Char}
    (hb : ∀ j (hj : j < seg.length), b.get! (o + j) = UInt8.ofNat (seg[j]'hj).toNat)
    (hs : ∀ c ∈ seg, hexV c.toNat < 16) :
    ∀ k ≤ seg.length, CFSG.Monster.B.Max2.Native.hexAt b o k = hexNum 0 (seg.take k)
  | 0, _ => rfl
  | k + 1, hk => by
    rw [CFSG.Monster.B.Max2.Native.hexAt, hexAt_seg hb hs k (by omega), List.take_add_one,
      List.getElem?_eq_getElem (by omega), Option.toList_some]
    unfold hexNum
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hb k (by omega), hexVal_eq (hs _ (List.getElem_mem _))]

theorem lineK_sound_at {cs : List Char} {wd n w a P : Nat}
    (ha : asciiK (cs.take (a + wd * n)) = true)
    (h : lineK wd n w P (cs.drop a) = true) :
    ∀ i < n, CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 (a + wd * i) wd =
      pg w (mask w) P i := by
  have h' : (Nat.blt 0 wd && lineRun wd n w P (cs.drop a) 0 0 0 0) = true := by
    change Bool.rec (motive := fun _ => Bool) false _ (Nat.blt 0 wd) = true at h
    cases hb : Nat.blt 0 wd <;> rw [hb] at h
    · exact absurd h Bool.false_ne_true
    · rw [Bool.true_and]
      exact h
  rw [Bool.and_eq_true] at h'
  have hwd : 0 < wd := lt_of_blt h'.1
  obtain ⟨g1, -⟩ := lineRun_all hwd n (cs.drop a) 0 0 (fun _ => 0) (by omega)
    (fun i hi => absurd hi (by omega)) (fld_congr (fld_zero w) (fun i => by simp)) h'.2
  intro i hi
  obtain ⟨f1, f2, f3⟩ := g1 i (Nat.zero_le i) hi
  have hcomm := Nat.mul_comm i wd
  rw [Nat.sub_zero, List.drop_drop] at f2 f3
  rw [Nat.sub_zero, List.length_drop] at f1
  have hwi : wd * i + wd ≤ wd * n := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left wd hi
  have hlen : ((cs.drop (a + i * wd)).take wd).length = wd := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.mul_comm] at f1
    omega
  rw [f3, hexAt_seg (o := a + wd * i) ?_ f2 wd (by omega), List.take_of_length_le (by omega)]
  intro j hj
  have hj' : j < wd := by omega
  have hl : a + wd * i + j < cs.length := by
    rw [Nat.mul_comm] at f1
    omega
  rw [get!_toUTF8 (asciiK_spec ha) (by omega) hl]
  simp only [List.getElem_take, List.getElem_drop]
  congr 3
  rw [Nat.mul_comm i wd]

theorem lineK_sound {cs : List Char} {wd n w L P : Nat} (ha : asciiK (cs.take ((L + 1) * (wd * n + 1))) = true)
    (h : lineK wd n w P (cs.drop (L * (wd * n + 1))) = true) :
    ∀ i < n, CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8
      (L * (wd * n + 1) + wd * i) wd = pg w (mask w) P i := by
  refine lineK_sound_at (asciiK_of fun c hc => asciiK_spec ha c ?_) h
  have hle : L * (wd * n + 1) + wd * n ≤ (L + 1) * (wd * n + 1) := by
    rw [Nat.succ_mul]
    omega
  have e : cs.take (L * (wd * n + 1) + wd * n) =
      (cs.take ((L + 1) * (wd * n + 1))).take (L * (wd * n + 1) + wd * n) := by
    rw [List.take_take, Nat.min_eq_left hle]
  rw [e] at hc
  exact List.mem_of_mem_take hc

end CFSG.KS.Text

end
