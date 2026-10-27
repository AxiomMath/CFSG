module

public import Certificates.Data.Kernel.SurjK
public import Certificates.Data.CFSGNative.Bridge.SurjD
public import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
public import CFSG.Certificates.Kernel.Spor.DecLinesRead

public section

namespace CFSG.KC.SurjK.Pf

open CFSG.KC.SurjK CFSG.KS.SporSch.LyTxt CFSG.KC.Loop
open CFSG.Sporadic.Bridge.SurjD.Native

@[expose] def lw (l : List Char) : List Int := (l.splitOnP (· == ' ')).filterMap tv

@[expose] def words (cs : List Char) : List (List Int) :=
  ((cs.splitOnP (· == '\n')).filter fun l => !l.isEmpty).map lw

theorem parseWords_ofList (cs : List Char) : parseWords (String.ofList cs) = (words cs).toArray := by
  unfold parseWords words
  rw [splitOn_nl, List.splitOnPPrepend_nil_right, List.filter_map, List.map_map]
  have e1 : ((fun l : String => !l.isEmpty) ∘ String.ofList) = fun l : List Char => !l.isEmpty := by
    funext l
    simp only [Function.comp_apply, CFSG.KS.DecLines.ofList_isEmpty]
  have e2 : parseLine ∘ String.ofList = lw := by
    funext l
    simp only [Function.comp_apply, parseLine, lw]
    rw [splitOn_sp, List.splitOnPPrepend_nil_right, List.filterMap_map]
    rfl
  rw [e1, e2]

theorem nl_false {c : Char} (h : c ≠ '\n') : (c == '\n') = false := by
  simpa using h

theorem words_nil : words [] = [] := by
  simp [words]

theorem words_nl (r : List Char) : words ('\n' :: r) = words r := by
  unfold words
  rw [List.splitOnP_cons_eq_ite_modifyHead]
  simp

theorem words_line {line : List Char} (hl : ∀ c ∈ line, c ≠ '\n') (hne : line ≠ []) :
    words line = [lw line] := by
  unfold words
  rw [List.splitOnP_eq_singleton (fun c hc => nl_false (hl c hc))]
  cases line with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

theorem words_line_nl {line : List Char} (hl : ∀ c ∈ line, c ≠ '\n') (hne : line ≠ [])
    (r : List Char) : words (line ++ '\n' :: r) = lw line :: words r := by
  unfold words
  rw [List.splitOnP_append_cons_of_forall_mem (fun c hc => nl_false (hl c hc)) '\n' rfl r]
  cases line with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

theorem sp_false {c : Char} (h : c ≠ ' ') : (c == ' ') = false := by
  simpa using h

theorem lw_tok {tok : List Char} (ht : ∀ c ∈ tok, c ≠ ' ') {x : Int} (hx : tv tok = some x) :
    lw tok = [x] := by
  unfold lw
  rw [List.splitOnP_eq_singleton (fun c hc => sp_false (ht c hc))]
  simp [hx]

theorem lw_tok_sp {tok : List Char} (ht : ∀ c ∈ tok, c ≠ ' ') {x : Int} (hx : tv tok = some x)
    (r : List Char) : lw (tok ++ ' ' :: r) = x :: lw r := by
  unfold lw
  rw [List.splitOnP_append_cons_of_forall_mem (fun c hc => sp_false (ht c hc)) ' ' rfl r]
  simp [hx]

@[expose] def Tok (o : List Char) (st sg v : Nat) : Prop :=
  (st = 0 ∧ o = []) ∨ (st = 1 ∧ sg = 1 ∧ v = 0 ∧ o = ['-']) ∨
  (st = 2 ∧ ∃ ds : List Char, ds ≠ [] ∧ (∀ c ∈ ds, c.isDigit = true) ∧
    v = Nat.ofDigitChars 10 ds 0 ∧ ((sg = 0 ∧ o = ds) ∨ (sg = 1 ∧ o = '-' :: ds)))

theorem tok_chars {o : List Char} {st sg v : Nat} (h : Tok o st sg v) :
    ∀ c ∈ o, c ≠ ' ' ∧ c ≠ '\n' := by
  intro c hc
  rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, ds, -, hd, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
  · simp at hc
  · simp at hc
    subst hc
    decide
  · have := hd c hc
    constructor <;> rintro rfl <;> exact absurd this (by decide)
  · rcases List.mem_cons.1 hc with rfl | hc
    · decide
    · have := hd c hc
      constructor <;> rintro rfl <;> exact absurd this (by decide)

theorem tok_tv {o : List Char} {sg v : Nat} (h : Tok o 2 sg v) : tv o = some (tokV sg v) := by
  rcases h with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, ds, hne, hd, rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · omega
  · omega
  · rw [tv_pos hd hne]
    rfl
  · rw [tv_neg hd hne]
    rfl

theorem digV_lt {c : Nat} (h : digV c < 10) : 48 ≤ c ∧ c ≤ 57 ∧ digV c = c - 48 := by
  unfold digV at h ⊢
  cases hb : CFSG.KLie.CT.andB (Nat.ble 48 c) (Nat.ble c 57)
  · rw [hb] at h
    exact absurd h (Nat.lt_irrefl 10)
  · have hb' : Nat.ble 48 c = true ∧ Nat.ble c 57 = true := by
      revert hb
      cases Nat.ble 48 c <;> cases Nat.ble c 57 <;> decide
    exact ⟨Nat.le_of_ble_eq_true hb'.1, Nat.le_of_ble_eq_true hb'.2, rfl⟩

theorem isDigit_of_le {ch : Char} (h1 : 48 ≤ ch.toNat) (h2 : ch.toNat ≤ 57) : ch.isDigit = true :=
  isDigit_of (by rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]; exact ⟨h1, h2⟩)

theorem ne_of_digit {ch : Char} (h1 : 48 ≤ ch.toNat) (h2 : ch.toNat ≤ 57) :
    ch ≠ '\n' ∧ ch ≠ ' ' := by
  constructor <;> rintro rfl <;> simp at h1

@[expose] def Res (o cs : List Char) (L : List (List Int)) (W : List Int) (ln : Nat) : Prop :=
  (ln = 0 → words cs = L) ∧
  (ln ≠ 0 → ∃ line, (∀ c ∈ line, c ≠ '\n') ∧ lw line = W ∧
    ((o ++ cs = line ∧ L = []) ∨ ∃ r, o ++ cs = line ++ '\n' :: r ∧ words r = L))

theorem nilB_true {α : Type} {L : List α} (h : nilB L = true) : L = [] := by
  cases L with
  | nil => rfl
  | cons _ _ => exact absurd h Bool.false_ne_true

theorem strictB_m (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem wordsRun_cons (ch : Char) (cs : List Char) (L : List (List Int)) (W : List Int)
    (st sg v ln : Nat) : wordsRun (ch :: cs) L W st sg v ln =
      CFSG.KC.M1F2.strictB (Char.toNat ch) fun c =>
      bIf(Nat.blt (digV c) 10,
        bIf(Nat.beq st 0,
          bIf(Nat.beq ln 0,
            List.rec (motive := fun _ => Bool) false
              (fun W' L' _ => wordsRun cs L' W' 2 0 (digV c) 1) L,
            wordsRun cs L W 2 0 (digV c) 1),
          wordsRun cs L W 2 sg (Nat.add (Nat.mul v 10) (digV c)) 1),
      bIf(Nat.beq c 45, bAnd(Nat.beq st 0,
          bIf(Nat.beq ln 0,
            List.rec (motive := fun _ => Bool) false
              (fun W' L' _ => wordsRun cs L' W' 1 1 0 1) L,
            wordsRun cs L W 1 1 0 1)),
      bIf(Nat.beq c 32, bAnd(Nat.beq st 2,
          List.rec (motive := fun _ => Bool) false
            (fun x xs _ => bAnd(decide (x = tokV sg v), wordsRun cs L xs 0 0 0 1)) W),
      bIf(Nat.beq c 10,
        bIf(Nat.beq st 2,
          List.rec (motive := fun _ => Bool) false (fun x xs _ =>
            bAnd(decide (x = tokV sg v), bAnd(nilB xs, wordsRun cs L [] 0 0 0 0))) W,
          bAnd(Nat.beq st 0, bAnd(Nat.beq ln 0, wordsRun cs L W 0 0 0 0))),
        false)))) := rfl

theorem run_sound : ∀ (cs o : List Char) (L : List (List Int)) (W : List Int) (st sg v ln : Nat),
    Tok o st sg v → (ln = 0 → o = []) → wordsRun cs L W st sg v ln = true → Res o cs L W ln
  | [], o, L, W, st, sg, v, ln, ht, hln, h => by
    change Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (nilB L) (nilB W)) (Nat.beq st 0))
      (List.rec (motive := fun _ => Bool) false (fun x xs _ =>
        Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (nilB L) (nilB xs)) (decide (x = tokV sg v))) W)
      (Nat.beq st 2) = true at h
    cases h2 : Nat.beq st 2
    · rw [h2] at h
      simp only [bAnd_eqT, Bool.and_eq_true] at h
      obtain ⟨h0, hW, hL⟩ := h
      have hst := Nat.eq_of_beq_eq_true h0
      rw [nilB_true hW, nilB_true hL]
      refine ⟨fun _ => words_nil, fun _ => ⟨[], by simp, by simp [lw, tv_nil], Or.inl ⟨?_, rfl⟩⟩⟩
      rcases ht with ⟨-, rfl⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · rfl
      · omega
      · omega
    · rw [h2] at h
      have hst := Nat.eq_of_beq_eq_true h2
      subst hst
      rcases W with _ | ⟨x, xs⟩
      · exact absurd h Bool.false_ne_true
      · simp only [bAnd_eqT, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hx, hxs, hL⟩ := h
        rw [nilB_true hxs, nilB_true hL, hx]
        refine ⟨fun h0 => ?_, fun _ => ⟨o, fun c hc => (tok_chars ht c hc).2,
          lw_tok (fun c hc => (tok_chars ht c hc).1) (tok_tv ht), Or.inl ⟨by simp, rfl⟩⟩⟩
        rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, ds, hne, -, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
        · omega
        · omega
        · exact absurd (hln h0) hne
        · exact absurd (hln h0) (by simp)
  | ch :: cs, o, L, W, st, sg, v, ln, ht, hln, h => by
    rw [wordsRun_cons, strictB_m] at h
    have hlnz : o ≠ [] → ln ≠ 0 := fun ho h0 => ho (hln h0)
    by_cases hd : Nat.blt (digV ch.toNat) 10 = true
    · simp only [hd] at h
      obtain ⟨h48, h57, hdv⟩ := digV_lt (Nat.blt_eq.mp hd)
      have hch := ne_of_digit h48 h57
      have hdig := isDigit_of_le h48 h57
      have hone : Tok [ch] 2 0 (digV ch.toNat) := Or.inr (Or.inr ⟨rfl, [ch], by simp,
        by simpa using hdig, by rw [hdv, ← List.nil_append [ch], ofDigitChars_snoc]; simp,
        Or.inl ⟨rfl, rfl⟩⟩)
      by_cases hs0 : Nat.beq st 0 = true
      · simp only [hs0] at h
        have ho : o = [] := by
          rcases ht with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · exact h1
          · rw [Nat.eq_of_beq_eq_true hs0] at h1
            omega
          · rw [Nat.eq_of_beq_eq_true hs0] at h1
            omega
        subst ho
        by_cases hl0 : Nat.beq ln 0 = true
        · simp only [hl0] at h
          have hln0 := Nat.eq_of_beq_eq_true hl0
          rcases L with _ | ⟨W', L'⟩
          · exact absurd h Bool.false_ne_true
          · obtain ⟨-, hR⟩ := run_sound cs [ch] L' W' 2 0 (digV ch.toNat) 1 hone (by omega) h
            obtain ⟨line, hnl, hlw, hrest⟩ := hR (by omega)
            refine ⟨fun _ => ?_, fun h0 => absurd hln0 h0⟩
            have hne : line ≠ [] := by
              rintro rfl
              rcases hrest with ⟨e, -⟩ | ⟨r, e, -⟩
              · simp at e
              · simp only [List.singleton_append, List.nil_append, List.cons.injEq] at e
                exact hch.1 e.1
            rcases hrest with ⟨e, hL⟩ | ⟨r, e, hr⟩
            · rw [List.singleton_append] at e
              rw [e, words_line hnl hne, hlw, hL]
            · rw [List.singleton_append] at e
              rw [e, words_line_nl hnl hne, hlw, hr]
        · simp only [Bool.not_eq_true] at hl0
          simp only [hl0] at h
          have hln0 : ln ≠ 0 := Nat.ne_of_beq_eq_false hl0
          obtain ⟨-, hR⟩ := run_sound cs [ch] L W 2 0 (digV ch.toNat) 1 hone (by omega) h
          refine ⟨fun h0 => absurd h0 hln0, fun _ => ?_⟩
          obtain ⟨line, hnl, hlw, hrest⟩ := hR (by omega)
          exact ⟨line, hnl, hlw, by simpa using hrest⟩
      · simp only [Bool.not_eq_true] at hs0
        simp only [hs0] at h
        have hst : st ≠ 0 := Nat.ne_of_beq_eq_false hs0
        have ht' : Tok (o ++ [ch]) 2 sg (v * 10 + digV ch.toNat) := by
          rcases ht with ⟨h1, -⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, ds, hne, hds, rfl, hcase⟩
          · exact absurd h1 hst
          · refine Or.inr (Or.inr ⟨rfl, [ch], by simp, by simpa using hdig, ?_, Or.inr ⟨rfl, rfl⟩⟩)
            rw [hdv, ← List.nil_append [ch], ofDigitChars_snoc]
            simp
          · refine Or.inr (Or.inr ⟨rfl, ds ++ [ch], by simp,
              fun c hc => by
                rcases List.mem_append.1 hc with hc | hc
                · exact hds c hc
                · rw [List.mem_singleton] at hc
                  rw [hc]
                  exact hdig, by rw [ofDigitChars_snoc, hdv], ?_⟩)
            rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, by simp⟩
        have hone' : o ≠ [] := by
          rcases ht with ⟨h1, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, ds, hne, -, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
          · exact absurd h1 hst
          · simp
          · exact hne
          · simp
        have hln0 := hlnz hone'
        obtain ⟨-, hR⟩ := run_sound cs (o ++ [ch]) L W 2 sg (v * 10 + digV ch.toNat) 1 ht' (by omega) h
        refine ⟨fun h0 => absurd h0 hln0, fun _ => ?_⟩
        obtain ⟨line, hnl, hlw, hrest⟩ := hR (by omega)
        exact ⟨line, hnl, hlw, by simpa using hrest⟩
    · simp only [Bool.not_eq_true] at hd
      simp only [hd] at h
      by_cases h45 : Nat.beq ch.toNat 45 = true
      · have hch : ch = '-' := char_of_beq h45 (by decide)
        subst hch
        simp only [h45, bAnd_eqT, Bool.and_eq_true] at h
        obtain ⟨hs0, h⟩ := h
        have ho : o = [] := by
          rcases ht with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · exact h1
          · rw [Nat.eq_of_beq_eq_true hs0] at h1
            omega
          · rw [Nat.eq_of_beq_eq_true hs0] at h1
            omega
        subst ho
        have hone : Tok ['-'] 1 1 0 := Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
        by_cases hl0 : Nat.beq ln 0 = true
        · simp only [hl0] at h
          have hln0 := Nat.eq_of_beq_eq_true hl0
          rcases L with _ | ⟨W', L'⟩
          · exact absurd h Bool.false_ne_true
          · obtain ⟨-, hR⟩ := run_sound cs ['-'] L' W' 1 1 0 1 hone (by omega) h
            obtain ⟨line, hnl, hlw, hrest⟩ := hR (by omega)
            refine ⟨fun _ => ?_, fun h0 => absurd hln0 h0⟩
            have hne : line ≠ [] := by
              rintro rfl
              rcases hrest with ⟨e, -⟩ | ⟨r, e, -⟩
              · simp at e
              · simp only [List.singleton_append, List.nil_append, List.cons.injEq] at e
                exact absurd e.1 (by decide)
            rcases hrest with ⟨e, hL⟩ | ⟨r, e, hr⟩
            · rw [List.singleton_append] at e
              rw [e, words_line hnl hne, hlw, hL]
            · rw [List.singleton_append] at e
              rw [e, words_line_nl hnl hne, hlw, hr]
        · simp only [Bool.not_eq_true] at hl0
          simp only [hl0] at h
          have hln0 : ln ≠ 0 := Nat.ne_of_beq_eq_false hl0
          obtain ⟨-, hR⟩ := run_sound cs ['-'] L W 1 1 0 1 hone (by omega) h
          refine ⟨fun h0 => absurd h0 hln0, fun _ => ?_⟩
          obtain ⟨line, hnl, hlw, hrest⟩ := hR (by omega)
          exact ⟨line, hnl, hlw, by simpa using hrest⟩
      · simp only [Bool.not_eq_true] at h45
        simp only [h45] at h
        by_cases h32 : Nat.beq ch.toNat 32 = true
        · have hch : ch = ' ' := char_of_beq h32 (by decide)
          subst hch
          simp only [h32, bAnd_eqT, Bool.and_eq_true] at h
          obtain ⟨hs2, h⟩ := h
          have hst := Nat.eq_of_beq_eq_true hs2
          subst hst
          rcases W with _ | ⟨x, xs⟩
          · exact absurd h Bool.false_ne_true
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨hx, h⟩ := h
            have hone' : o ≠ [] := by
              rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, ds, hne, -, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
              · omega
              · omega
              · exact hne
              · simp
            have hln0 := hlnz hone'
            obtain ⟨-, hR⟩ := run_sound cs [] L xs 0 0 0 1 (Or.inl ⟨rfl, rfl⟩) (by omega) h
            refine ⟨fun h0 => absurd h0 hln0, fun _ => ?_⟩
            obtain ⟨line, hnl, hlw, hrest⟩ := hR (by omega)
            refine ⟨o ++ ' ' :: line, fun c hc => ?_, ?_, ?_⟩
            · rcases List.mem_append.1 hc with hc | hc
              · exact (tok_chars ht c hc).2
              · rcases List.mem_cons.1 hc with rfl | hc
                · decide
                · exact hnl c hc
            · rw [lw_tok_sp (fun c hc => (tok_chars ht c hc).1) (tok_tv ht), hlw, hx]
            · rcases hrest with ⟨e, hL⟩ | ⟨r, e, hr⟩
              · rw [List.nil_append] at e
                exact Or.inl ⟨by rw [e], hL⟩
              · rw [List.nil_append] at e
                exact Or.inr ⟨r, by rw [e]; simp, hr⟩
        · simp only [Bool.not_eq_true] at h32
          simp only [h32] at h
          by_cases h10 : Nat.beq ch.toNat 10 = true
          · have hch : ch = '\n' := char_of_beq h10 (by decide)
            subst hch
            simp only [h10] at h
            by_cases hs2 : Nat.beq st 2 = true
            · simp only [hs2] at h
              have hst := Nat.eq_of_beq_eq_true hs2
              subst hst
              rcases W with _ | ⟨x, xs⟩
              · exact absurd h Bool.false_ne_true
              · simp only [bAnd_eqT, Bool.and_eq_true, decide_eq_true_eq] at h
                obtain ⟨hx, hxs, h⟩ := h
                have hone' : o ≠ [] := by
                  rcases ht with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, ds, hne, -, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
                  · omega
                  · omega
                  · exact hne
                  · simp
                have hln0 := hlnz hone'
                obtain ⟨hR, -⟩ := run_sound cs [] L [] 0 0 0 0 (Or.inl ⟨rfl, rfl⟩) (fun _ => rfl) h
                refine ⟨fun h0 => absurd h0 hln0, fun _ => ⟨o, fun c hc => (tok_chars ht c hc).2,
                  ?_, Or.inr ⟨cs, rfl, hR rfl⟩⟩⟩
                rw [nilB_true hxs, lw_tok (fun c hc => (tok_chars ht c hc).1) (tok_tv ht), hx]
            · simp only [Bool.not_eq_true] at hs2
              simp only [hs2, bAnd_eqT, Bool.and_eq_true] at h
              obtain ⟨hs0, hl0, h⟩ := h
              have hst := Nat.eq_of_beq_eq_true hs0
              have hln0 := Nat.eq_of_beq_eq_true hl0
              subst hst hln0
              have ho : o = [] := hln rfl
              subst ho
              obtain ⟨hR, -⟩ := run_sound cs [] L W 0 0 0 0 (Or.inl ⟨rfl, rfl⟩) (fun _ => rfl) h
              exact ⟨fun _ => by rw [words_nl, hR rfl], fun h0 => absurd rfl h0⟩
          · simp only [Bool.not_eq_true] at h10
            simp only [h10] at h
            exact absurd h Bool.false_ne_true

end CFSG.KC.SurjK.Pf

end

public section

namespace CFSG.KC.SurjK

open CFSG.Sporadic.Bridge.SurjD.Native CFSG.KC.SurjK.Pf

theorem wordsK_sound_proved {cs : List Char} {L : List (List Int)} (h : wordsK cs L = true) :
    parseWords (String.ofList cs) = L.toArray := by
  change Bool.rec (motive := fun _ => Bool) false (wordsRun cs L [] 0 0 0 0)
    (L.all fun w => !nilB w) = true at h
  cases hL : L.all fun w => !nilB w
  · rw [hL] at h
    exact absurd h Bool.false_ne_true
  · rw [hL] at h
    obtain ⟨hR, -⟩ := run_sound cs [] L [] 0 0 0 0 (Or.inl ⟨rfl, rfl⟩) (fun _ => rfl) h
    rw [parseWords_ofList, hR rfl]

end CFSG.KC.SurjK

end
