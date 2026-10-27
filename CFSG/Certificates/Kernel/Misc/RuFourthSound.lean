module

public import Certificates.Data.Kernel.Misc.RuFourth
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Certificates.Data.Kernel.Spor.TextAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.WordsInputs
import CFSG.Certificates.Kernel.Misc.RuFourthSoundGen
import CFSG.Certificates.Kernel.Spor.TextAtSound
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Misc.RuFourth

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSporadicStandard.TwoRu
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.Bridge.SurjD.Native

theorem fourthK_sound {R RI : Nat → Nat} {P0 : List Int} {y x₁ x₂ : Nat}
    (hR : ∀ k < 3,
      CFSG.Monster.B.Co2.Native.hexTable 4 16240 (16240 * k) ruRhoText = unpack 16240 14 (R k))
    (hP : (ruSpec ()).surjWords[0]! = P0)
    (hperm : ∀ l < 3, permOK 16240 14 16383 (16240 * 14) (R l) (RI l) = true)
    (hl : letters3 P0 = true) (hz : zOK R RI P0 y = true)
    (h₁ : oneP R RI P0 (wordFrom R RI [-3, 2] idP) 320 x₁ = true)
    (h₂ : oneP R RI P0 (wordFrom R RI [-2, -1, -3, -1, -3, -1, 3, -2, -1, -3, -1, -3, -1, 3] idP)
      48 x₂ = true) :
    ruFourthCheck = true :=
  FourthGen.inst (fourthK_sound_gen ruRhoText ruSurjText ruImgText) hR hP hperm hl hz h₁ h₂

theorem wordFrom_append (R RI : Nat → Nat) (a b : List Int) (s : Nat) :
    wordFrom R RI (a ++ b) s = wordFrom R RI a (wordFrom R RI b s) := by
  induction a with
  | nil => rfl
  | cons z t ih =>
    rw [List.cons_append]
    exact congrArg (fun X => strictN X (fun T => strictN (CFSG.KS.Mathieu.icode z) (fun c =>
      pcomp (nat_lit 16240) (nat_lit 14) (nat_lit 16383) (letterP R RI c) T))) ih

section Ints

open CFSG.KS.SporSch.LyTxt (tv tv_pos tv_neg tv_nil ofDigitChars_snoc isDigit_of char_of_beq
  ne_of_beq_false)

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem strictL_eq (y : Nat) (k : Nat → List Int) : intsGo.strictL y k = k y := by
  cases y <;> rfl

private theorem fmtGo_cons (ch : Char) (cs : List Char) (s : Nat) :
    fmtGo (ch :: cs) s = (fun c =>
      bIf(Nat.beq c 10, bIf(Nat.beq s 0, true, Nat.beq s 2),
      bIf(bAnd(Nat.ble 48 c, Nat.ble c 57), bIf(bAnd(Nat.beq s 1, Nat.beq c 48), false, fmtGo cs 2),
      bIf(Nat.beq c 45, bIf(Nat.beq s 0, fmtGo cs 1, bIf(Nat.beq s 3, fmtGo cs 1, false)),
      bIf(Nat.beq c 32, bIf(Nat.beq s 2, fmtGo cs 0, false), false))))) (Char.toNat ch) := by
  unfold fmtGo
  dsimp only
  exact strictB_eq' _ _

private theorem intsGo_cons (ch : Char) (cs : List Char) (v : Nat) (neg st : Bool) :
    intsGo (ch :: cs) v neg st = (fun c =>
      Bool.rec (motive := fun _ => List Int)
        (Bool.rec (motive := fun _ => List Int)
          (Bool.rec (motive := fun _ => List Int)
            (intsGo cs (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) neg true)
            (intsGo cs (nat_lit 0) true false) (Nat.beq c (nat_lit 45)))
          (Bool.rec (motive := fun _ => List Int) (intsGo cs (nat_lit 0) false false)
            (List.cons (Bool.rec (motive := fun _ => Int) (Int.ofNat v) (Int.negSucc (Nat.pred v)) neg)
              (intsGo cs (nat_lit 0) false false)) st)
          (Nat.beq c (nat_lit 32)))
        (Bool.rec (motive := fun _ => List Int) [] [Bool.rec (motive := fun _ => Int)
          (Int.ofNat v) (Int.negSucc (Nat.pred v)) neg] st)
        (Nat.beq c (nat_lit 10))) (Char.toNat ch) := by
  unfold intsGo
  dsimp only
  exact strictL_eq _ _

private def IState (s v : Nat) (neg st : Bool) (acc : List Char) : Prop :=
  ((s = 3 ∨ s = 0) ∧ acc = [] ∧ v = 0 ∧ neg = false ∧ st = false) ∨
  (s = 1 ∧ acc = ['-'] ∧ v = 0 ∧ neg = true ∧ st = false) ∨
  (s = 2 ∧ st = true ∧ ∃ ds : List Char, ds ≠ [] ∧ (∀ c ∈ ds, c.isDigit = true) ∧
    v = Nat.ofDigitChars 10 ds 0 ∧ acc = (if neg then '-' :: ds else ds).reverse ∧
    (neg = true → 0 < v))

private theorem tv_close {v : Nat} {neg : Bool} {acc : List Char} {s : Nat} {st : Bool}
    (h : IState s v neg st acc) (hs : s = 2) :
    tv acc.reverse = some (Bool.rec (motive := fun _ => Int) (Int.ofNat v) (Int.negSucc (Nat.pred v)) neg) := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, ds, hne, hd, rfl, rfl, hpos⟩
  · omega
  · omega
  cases neg
  · rw [if_neg (by decide), List.reverse_reverse, tv_pos hd hne]
    rfl
  · rw [if_pos rfl, List.reverse_reverse, tv_neg hd hne]
    have := hpos rfl
    change some (-((Nat.ofDigitChars 10 ds 0 : Nat) : Int)) = some (Int.negSucc (Nat.ofDigitChars 10 ds 0 - 1))
    congr 1
    rw [Int.negSucc_eq]
    omega

private theorem close_eq {v : Nat} {neg : Bool} {acc : List Char} {s : Nat} {st : Bool}
    (h : IState s v neg st acc) (hs : s = 0 ∨ s = 2) :
    Bool.rec (motive := fun _ => List Int) [] [Bool.rec (motive := fun _ => Int) (Int.ofNat v)
      (Int.negSucc (Nat.pred v)) neg] st = [acc.reverse].filterMap tv := by
  rcases hs with rfl | rfl
  · rcases h with ⟨-, rfl, -, -, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [List.reverse_nil, List.filterMap_cons, tv_nil]
      rfl
    · omega
    · omega
  · have hst : st = true := by
      rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
      · omega
      · omega
      · exact h
    subst hst
    rw [List.filterMap_cons, tv_close h rfl]
    rfl

private theorem nl_state {s : Nat} (h : Bool.rec (motive := fun _ => Bool) (Nat.beq s 2) true (Nat.beq s 0) = true) :
    s = 0 ∨ s = 2 := by
  cases h0 : Nat.beq s 0
  · rw [h0] at h
    exact Or.inr (Nat.eq_of_beq_eq_true h)
  · exact Or.inl (Nat.eq_of_beq_eq_true h0)

private theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem state_cases {s v : Nat} {neg st : Bool} {acc : List Char} (h : IState s v neg st acc) :
    s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by
  rcases h with ⟨h | h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

private theorem intsGo_spec : ∀ (cs : List Char) (s v : Nat) (neg st : Bool) (acc : List Char),
    IState s v neg st acc → fmtGo cs s = true →
    intsGo cs v neg st =
      (List.splitOnPPrepend (· == ' ') (cs.takeWhile fun c => !(c == '\n')) acc).filterMap tv
  | [], s, v, neg, st, acc, hS, h => by
    rw [List.takeWhile_nil, List.splitOnPPrepend_nil]
    exact close_eq hS (nl_state h)
  | ch :: cs, s, v, neg, st, acc, hS, h => by
    rw [fmtGo_cons] at h
    rw [intsGo_cons]
    dsimp only at h ⊢
    by_cases h10 : Nat.beq ch.toNat 10 = true
    · rw [h10] at h ⊢
      dsimp only at h ⊢
      have hc : ch = '\n' := char_of_beq h10 (by decide)
      rw [List.takeWhile_cons_of_neg (by rw [hc]; decide), List.splitOnPPrepend_nil]
      exact close_eq hS (nl_state h)
    have h10' : Nat.beq ch.toNat 10 = false := Bool.eq_false_iff.mpr h10
    rw [h10'] at h ⊢
    dsimp only at h ⊢
    have hnl : ch ≠ '\n' := ne_of_beq_false h10' (by decide)
    rw [List.takeWhile_cons_of_pos (by simpa using hnl)]
    by_cases hd : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = true
    ·
      have hd' := hd
      rw [Bool.and_eq_true] at hd'
      rw [hd'.1, hd'.2] at h
      dsimp only at h
      have hdig : ch.isDigit = true := isDigit_of hd
      have h1 := Nat.le_of_ble_eq_true hd'.1
      have h2 := Nat.le_of_ble_eq_true hd'.2
      rw [beq_false (by omega : ch.toNat ≠ 32), beq_false (by omega : ch.toNat ≠ 45)]
      dsimp only
      have hsp : (ch == ' ') = false := by
        have := ne_of_beq_false (c := ch) (n := 32) (beq_false (by omega)) (by decide)
        simpa using this
      rw [List.splitOnPPrepend_cons_neg (p := fun x => x == ' ') hsp]
      have hone : Nat.ofDigitChars 10 [ch] 0 = 0 * 10 + (ch.toNat - 48) := by
        have := ofDigitChars_snoc [] ch
        rwa [List.nil_append, Nat.ofDigitChars_nil] at this
      rcases hS with ⟨hs, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, ds, hne, hds, rfl, rfl, hpos⟩
      · have hs1 : Nat.beq s 1 = false := beq_false (by omega)
        rw [hs1] at h
        dsimp only at h
        refine intsGo_spec cs 2 _ false true [ch] (Or.inr (Or.inr ⟨rfl, rfl, [ch], by simp,
          by simpa using hdig, ?_, rfl, by simp⟩)) h
        rw [hone]
        rfl
      · have h48 : Nat.beq ch.toNat 48 = false := by
          cases hb : Nat.beq ch.toNat 48
          · rfl
          · rw [hb] at h
            exact absurd h Bool.false_ne_true
        rw [h48] at h
        refine intsGo_spec cs 2 _ true true [ch, '-'] (Or.inr (Or.inr ⟨rfl, rfl, [ch], by simp,
          by simpa using hdig, ?_, rfl, fun _ => ?_⟩)) h
        · rw [hone]
          rfl
        · have : ch.toNat ≠ 48 := fun e => by rw [e] at h48; exact absurd h48 (by decide)
          change 0 < 0 * 10 + (ch.toNat - 48)
          omega
      · rw [(beq_false (by omega) : Nat.beq 2 1 = false)] at h
        dsimp only at h
        refine intsGo_spec cs 2 _ neg true (ch :: (if neg then '-' :: ds else ds).reverse)
          (Or.inr (Or.inr ⟨rfl, rfl, ds ++ [ch], by simp, fun c hc => ?_, ?_, ?_, fun hn => ?_⟩)) h
        · rcases List.mem_append.mp hc with hc | hc
          · exact hds c hc
          · rw [List.mem_singleton.mp hc]
            exact hdig
        · rw [ofDigitChars_snoc]
          rfl
        · cases neg <;> simp
        · have := hpos hn
          change 0 < Nat.ofDigitChars 10 ds 0 * 10 + (ch.toNat - 48)
          omega
    have hd' : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = false := Bool.eq_false_iff.mpr hd
    rw [Bool.and_eq_false_iff] at hd'
    have hfalse : Bool.rec (motive := fun _ => Bool) false (Nat.ble ch.toNat 57) (Nat.ble 48 ch.toNat) =
        false := by
      rcases hd' with e | e
      · rw [e]
      · rw [e]
        cases Nat.ble 48 ch.toNat <;> rfl
    rw [hfalse] at h
    dsimp only at h
    by_cases h45 : Nat.beq ch.toNat 45 = true
    ·
      rw [h45] at h
      dsimp only at h
      have hc : ch = '-' := char_of_beq h45 (by decide)
      rw [beq_false (by rw [hc]; decide : ch.toNat ≠ 32), h45]
      dsimp only
      rw [List.splitOnPPrepend_cons_neg (p := fun x => x == ' ') (by rw [hc]; decide), hc]
      rcases state_cases hS with rfl | rfl | rfl | rfl
      · rcases hS with ⟨-, rfl, rfl, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact intsGo_spec cs 1 0 true false ['-'] (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) h
        · omega
        · omega
      · exact absurd (h : false = true) Bool.false_ne_true
      · exact absurd (h : false = true) Bool.false_ne_true
      · rcases hS with ⟨-, rfl, rfl, rfl, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact intsGo_spec cs 1 0 true false ['-'] (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩)) h
        · omega
        · omega
    have h45' : Nat.beq ch.toNat 45 = false := Bool.eq_false_iff.mpr h45
    rw [h45'] at h
    dsimp only at h
    by_cases h32 : Nat.beq ch.toNat 32 = true
    ·
      rw [h32] at h ⊢
      dsimp only at h ⊢
      have hc : ch = ' ' := char_of_beq h32 (by decide)
      rw [List.splitOnPPrepend_cons_pos (p := fun x => x == ' ') (by rw [hc]; decide)]
      rcases state_cases hS with rfl | rfl | rfl | rfl
      · exact absurd (h : false = true) Bool.false_ne_true
      · exact absurd (h : false = true) Bool.false_ne_true
      · have hst : st = true := by
          rcases hS with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h', -⟩
          · omega
          · omega
          · exact h'
        subst hst
        rw [List.filterMap_cons, tv_close hS rfl]
        dsimp only
        rw [← List.splitOnPPrepend_nil_right]
        exact congrArg (List.cons _) (intsGo_spec cs 0 0 false false [] (Or.inl ⟨Or.inr rfl, rfl, rfl, rfl, rfl⟩) h)
      · exact absurd (h : false = true) Bool.false_ne_true
    · have h32' : Nat.beq ch.toNat 32 = false := Bool.eq_false_iff.mpr h32
      rw [h32'] at h
      exact absurd (h : false = true) Bool.false_ne_true

private theorem isEmpty_ofList (l : List Char) : (String.ofList l).isEmpty = l.isEmpty := by
  cases l with
  | nil => rfl
  | cons c l => simp

theorem intsK_sound {cs : List Char} (h : wordsTextOK cs = true) :
    (parseWords (String.ofList cs))[0]! = intsK cs := by
  have hspec := intsGo_spec cs 3 0 false false [] (Or.inl ⟨Or.inl rfl, rfl, rfl, rfl, rfl⟩) h
  set l := cs.takeWhile fun c => !(c == '\n') with hl
  have hne : l ≠ [] := by
    cases cs with
    | nil => exact absurd (h : false = true) Bool.false_ne_true
    | cons ch cs' =>
      by_cases hc : ch = '\n'
      · subst hc
        exact absurd (h : false = true) Bool.false_ne_true
      · rw [hl, List.takeWhile_cons_of_pos (by simpa using hc)]
        exact List.cons_ne_nil _ _
  have hlp : ∀ x ∈ l, (x == '\n') = false := fun x hx => by
    have := List.all_eq_true.mp List.all_takeWhile x hx
    simpa using this
  have hsplit : ∃ rest, List.splitOnP (· == '\n') cs = l :: rest := by
    have e := List.takeWhile_append_dropWhile (p := fun c => !(c == '\n')) (l := cs)
    rw [← hl] at e
    rcases hd : cs.dropWhile (fun c => !(c == '\n')) with _ | ⟨d, r⟩
    · rw [hd, List.append_nil] at e
      refine ⟨[], ?_⟩
      rw [← e]
      exact List.splitOnP_eq_singleton hlp
    · have hd' : d = '\n' := by
        have := List.head_dropWhile_not (fun c => !(c == '\n')) (l := cs) (by rw [hd]; simp)
        simp only [hd, List.head_cons] at this
        simpa using this
      rw [hd, hd'] at e
      refine ⟨List.splitOnP (· == '\n') r, ?_⟩
      rw [← e]
      exact List.splitOnP_append_cons_of_forall_mem hlp '\n' rfl r
  obtain ⟨rest, hrest⟩ := hsplit
  unfold parseWords
  rw [CFSG.KS.SporSch.LyTxt.splitOn_nl, List.splitOnPPrepend_nil_right, hrest, List.map_cons,
    List.filter_cons_of_pos (by rw [isEmpty_ofList]; simpa using hne), List.map_cons]
  change parseLine (String.ofList l) = intsGo cs 0 false false
  rw [hspec]
  unfold parseLine
  rw [CFSG.KS.SporSch.LyTxt.splitOn_sp, List.filterMap_map]
  rfl

end Ints

theorem lineK_sound_at {cs : List Char} {wd n w a P : Nat}
    (ha : CFSG.KS.Text.asciiK (cs.take (a + wd * n)) = true)
    (h : CFSG.KS.Text.lineK wd n w P (cs.drop a) = true) :
    ∀ i < n, CFSG.Monster.B.Max2.Native.hexAt (String.ofList cs).toUTF8 (a + wd * i) wd =
      pg w (mask w) P i :=
  CFSG.KS.Text.lineK_sound_at ha h

theorem hexAt_eq (b : ByteArray) (o w : Nat) :
    CFSG.Monster.B.Co2.Native.hexAt b o w = CFSG.Monster.B.Max2.Native.hexAt b o w := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [CFSG.Monster.B.Co2.Native.hexAt, CFSG.Monster.B.Max2.Native.hexAt, ih]
    rfl

end CFSG.KC.Misc.RuFourth

end
