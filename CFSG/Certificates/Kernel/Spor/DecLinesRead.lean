module

public import Certificates.Data.Kernel.Spor.DecLines
public import CFSG.Sporadic.HNOddCore.InvArrays
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import all Init.Data.String.Defs
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Batteries.Tactic.Init
import Mathlib.Tactic.SplitIfs

public section

namespace CFSG.KS.DecLines

open CFSG.Sporadic.HNOddCore.InvData CFSG.YGroups.ModelNative

@[expose] def val (p : List Char) : Nat := Nat.ofDigitChars 10 p 0

@[expose] def toks (l : List Char) : List Nat :=
  ((l.splitOnP (· == ' ')).filter fun p => !p.isEmpty).map val

@[expose] def lns (d : List Char) : List (List Nat) :=
  ((d.splitOnP (· == '\n')).filter fun l => !l.isEmpty).map toks

theorem mem_splitOnP {p : Char → Bool} : ∀ (d : List Char), ∀ l ∈ d.splitOnP p, ∀ x ∈ l,
    x ∈ d ∧ p x = false
  | [], l, hl, x, hx => by
    rw [List.splitOnP_nil, List.mem_singleton] at hl
    subst hl
    exact absurd hx List.not_mem_nil
  | c :: d, l, hl, x, hx => by
    rw [List.splitOnP_cons_eq_ite_modifyHead] at hl
    split at hl
    · rcases List.mem_cons.1 hl with rfl | hl
      · exact absurd hx List.not_mem_nil
      · obtain ⟨h1, h2⟩ := mem_splitOnP d l hl x hx
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · next hc =>
      obtain ⟨h, t, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p d)
      rw [e, List.modifyHead_cons] at hl
      rcases List.mem_cons.1 hl with rfl | hl
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨List.mem_cons.2 (Or.inl rfl), by simpa using hc⟩
        · obtain ⟨h1, h2⟩ := mem_splitOnP d h (by rw [e]; exact List.mem_cons.2 (Or.inl rfl)) x hx
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · obtain ⟨h1, h2⟩ := mem_splitOnP d l (by rw [e]; exact List.mem_cons_of_mem _ hl) x hx
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem toks_digits {o : List Char} (ho : ∀ c ∈ o, c.isDigit = true) :
    toks o = if o.isEmpty then [] else [val o] := by
  unfold toks
  rw [List.splitOnP_eq_singleton (p := (· == ' ')) fun x hx => by
    have h := ho x hx
    cases e : (x == ' ')
    · rfl
    · rw [beq_iff_eq] at e
      subst e
      exact absurd h (by decide)]
  cases o <;> rfl

theorem toks_space {o : List Char} (ho : ∀ c ∈ o, c.isDigit = true) (r : List Char) :
    toks (o ++ ' ' :: r) = (if o.isEmpty then [] else [val o]) ++ toks r := by
  unfold toks
  rw [List.splitOnP_append_cons_of_forall_mem (p := (· == ' ')) (fun x hx => by
    have h := ho x hx
    cases e : (x == ' ')
    · rfl
    · rw [beq_iff_eq] at e
      subst e
      exact absurd h (by decide)) ' ' rfl r]
  cases o <;> rfl

theorem toNat!_of {s : String} {v : Nat} (h : s.toNat? = some v) : s.toNat! = v := by
  unfold String.toNat? String.Slice.toNat? at h
  unfold String.toNat! String.Slice.toNat!
  split at h
  · next hn =>
    rw [ite_eq_left hn]
    exact Option.some.inj h
  · exact absurd h (by simp)

theorem ofList_isEmpty (p : List Char) : (String.ofList p).isEmpty = p.isEmpty := by
  rw [Bool.eq_iff_iff, String.isEmpty_iff, String.ofList_eq_empty_iff, List.isEmpty_iff]

theorem foldl_pieces : ∀ (ps : List (List Char)) (acc : Array Nat),
    (∀ p ∈ ps, ∀ c ∈ p, c.isDigit = true) →
    (ps.map String.ofList).foldl (fun a t => if t.isEmpty then a else a.push t.toNat!) acc =
      acc ++ ((ps.filter fun p => !p.isEmpty).map val).toArray
  | [], acc, _ => by simp
  | p :: ps, acc, h => by
    have h' : ∀ q ∈ ps, ∀ c ∈ q, c.isDigit = true := fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.foldl_cons, ofList_isEmpty]
    by_cases hp : p.isEmpty = true
    · rw [ite_eq_left hp, foldl_pieces ps acc h', List.filter_cons_of_neg (by simp [hp])]
    · rw [ite_eq_right hp, foldl_pieces ps _ h', List.filter_cons_of_pos (by simpa using hp),
        List.map_cons, CFSG.KS.DecLines.toNat!_of (CFSG.KS.SporSch.LyTxt.toNat_digits
          (h p (List.mem_cons.2 (Or.inl rfl))) (by simpa using hp))]
      simp [val]

theorem parseNats_ofList {l : List Char} (hl : ∀ c ∈ l, c.isDigit = true ∨ c = ' ') :
    parseNats (String.ofList l) = (toks l).toArray := by
  unfold parseNats toks
  rw [CFSG.KS.SporSch.LyTxt.splitOn_sp, List.splitOnPPrepend_nil_right, foldl_pieces _ _ ?_]
  · simp
  · intro p hp c hc
    obtain ⟨h1, h2⟩ := mem_splitOnP l p hp c hc
    rcases hl c h1 with h | h
    · exact h
    · subst h
      exact absurd h2 (by decide)

theorem textLines_ofList (cs : List Char) : textLines (String.ofList cs) =
    ((cs.splitOnP (· == '\n')).filter fun l => !l.isEmpty).map String.ofList := by
  unfold textLines
  rw [CFSG.KS.SporSch.LyTxt.splitOn_nl, List.splitOnPPrepend_nil_right, List.filter_map]
  congr 1
  apply List.filter_congr
  intro l _
  simp only [Function.comp, ofList_isEmpty]

theorem encodeL_nil : encodeL [] = [] := rfl

theorem encodeL_cons (l : List Nat) (E : List (List Nat)) :
    encodeL (l :: E) = l.map Nat.succ ++ 0 :: encodeL E := by
  change List.rec (motive := fun _ => List Nat) (List.cons 0 (encodeL E))
    (fun x _ ih2 => List.cons (Nat.succ x) ih2) l = _
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (List.cons (Nat.succ x)) ih

theorem prefix_inj : ∀ (l l' X X' : List Nat), l.map Nat.succ ++ 0 :: X = l'.map Nat.succ ++ 0 :: X' →
    l = l' ∧ X = X'
  | [], [], X, X', h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l, b :: l', X, X', h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq, Nat.succ.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := prefix_inj l l' X X' h
    exact ⟨rfl, rfl⟩

theorem encodeL_inj : ∀ (E E' : List (List Nat)), encodeL E = encodeL E' → E = E'
  | [], [], _ => rfl
  | [], l :: E', h => by rw [encodeL_nil, encodeL_cons] at h; simp at h
  | l :: E, [], h => by rw [encodeL_nil, encodeL_cons] at h; simp at h
  | l :: E, l' :: E', h => by
    rw [encodeL_cons, encodeL_cons] at h
    obtain ⟨rfl, h2⟩ := prefix_inj _ _ _ _ h
    rw [encodeL_inj E E' h2]

@[expose] noncomputable def rest (d o : List Char) (ne : Bool) : List Nat :=
  match d.splitOnP (· == '\n') with
  | [] => []
  | r :: ls => (if (ne || !r.isEmpty) = true then (toks (o ++ r)).map Nat.succ ++ [0] else []) ++
      encodeL ((ls.filter fun l => !l.isEmpty).map toks)

theorem rest_init (d : List Char) : rest d [] false = encodeL (lns d) := by
  unfold rest lns
  obtain ⟨r, ls, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') d)
  rw [e]
  dsimp only
  cases hr : r.isEmpty
  · rw [List.filter_cons_of_pos (by simp [hr]), List.map_cons, encodeL_cons]
    simp
  · rw [List.filter_cons_of_neg (by simp [hr])]
    simp

theorem band_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem emit_true {t : Nat} {T : List Nat} {k : List Nat → Bool} (h : emit t T k = true) :
    ∃ R, T = t :: R ∧ k R = true := by
  cases T with
  | nil => exact absurd h Bool.false_ne_true
  | cons a R =>
    obtain ⟨h1, h2⟩ := band_true (a := Nat.beq a t) (b := k R) h
    exact ⟨R, by rw [Nat.eq_of_beq_eq_true h1], h2⟩

theorem emitIf_true {b : Bool} {t : Nat} {T : List Nat} {k : List Nat → Bool}
    (h : emitIf b t T k = true) : ∃ R, T = (if b = true then [t] else []) ++ R ∧ k R = true := by
  cases b
  · exact ⟨T, rfl, h⟩
  · obtain ⟨R, e, hk⟩ := emit_true h
    exact ⟨R, by rw [e]; rfl, hk⟩

theorem run_data (ch : Char) (cs : List Char) (cur : Nat) (num ne : Bool) (T : List Nat) :
    run (ch :: cs) false cur num ne T =
      if Nat.beq ch.toNat 10 = true then
        emitIf num (Nat.succ cur) T fun T => emitIf ne 0 T fun T => run cs false 0 false false T
      else if Nat.beq ch.toNat 32 = true then
        emitIf num (Nat.succ cur) T fun T => run cs false 0 false true T
      else if (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = true then
        run cs false (cur * 10 + (ch.toNat - 48)) true true T
      else false := by
  change Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (run cs false (Nat.add (Nat.mul cur 10) (Nat.sub ch.toNat 48)) true true T)
        (bAnd(Nat.ble 48 ch.toNat, Nat.ble ch.toNat 57)))
      (emitIf num (Nat.succ cur) T fun T => run cs false 0 false true T)
      (Nat.beq ch.toNat 32))
    (emitIf num (Nat.succ cur) T fun T => emitIf ne 0 T fun T => run cs false 0 false false T)
    (Nat.beq ch.toNat 10) = _
  cases Nat.beq ch.toNat 10 <;> cases Nat.beq ch.toNat 32 <;> cases Nat.ble 48 ch.toNat <;>
    cases Nat.ble ch.toNat 57 <;> rfl

theorem run_head (ch : Char) (cs : List Char) (ne : Bool) (T : List Nat) :
    run (ch :: cs) true 0 false ne T =
      if Nat.beq ch.toNat 10 = true then (ne && run cs false 0 false false T)
      else run cs true 0 false true T := by
  change Bool.rec (motive := fun _ => Bool) (run cs true 0 false true T)
    (Bool.rec (motive := fun _ => Bool) false (run cs false 0 false false T) ne)
    (Nat.beq ch.toNat 10) = _
  cases Nat.beq ch.toNat 10 <;> cases ne <;> rfl

theorem lf_of {ch : Char} (h : Nat.beq ch.toNat 10 = true) : ch = '\n' :=
  CFSG.KS.SporSch.LyTxt.char_of_beq h (by decide)

theorem sp_of {ch : Char} (h : Nat.beq ch.toNat 32 = true) : ch = ' ' :=
  CFSG.KS.SporSch.LyTxt.char_of_beq h (by decide)

theorem ne_lf {ch : Char} (h : ¬ Nat.beq ch.toNat 10 = true) : (ch == '\n') = false := by
  have h' : Nat.beq ch.toNat 10 = false := Bool.eq_false_iff.2 h
  have := CFSG.KS.SporSch.LyTxt.ne_of_beq_false h' (by decide)
  simpa using this

theorem rest_cons_ne {ch : Char} (h : (ch == '\n') = false) (d o : List Char) (ne : Bool) :
    rest (ch :: d) o ne = rest d (o ++ [ch]) true := by
  unfold rest
  obtain ⟨r, ls, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') d)
  rw [List.splitOnP_cons_eq_ite_modifyHead, ite_eq_right (by simp [h]), e, List.modifyHead_cons]
  simp

theorem rest_lf (d o : List Char) (ne : Bool) :
    rest ('\n' :: d) o ne = (if ne = true then (toks o).map Nat.succ ++ [0] else []) ++
      encodeL (lns d) := by
  unfold rest
  rw [List.splitOnP_cons_eq_ite_modifyHead, ite_eq_left (by decide : ('\n' == '\n') = true)]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.or_false, List.append_nil, lns]

theorem val_nil : val [] = 0 := Nat.ofDigitChars_nil

theorem run_data_sound : ∀ (d o : List Char) (ne : Bool) (T : List Nat),
    (∀ c ∈ o, c.isDigit = true) → (o ≠ [] → ne = true) →
    run d false (val o) (!o.isEmpty) ne T = true →
    T = rest d o ne ∧ ∀ c ∈ d, c.isDigit = true ∨ c = ' ' ∨ c = '\n'
  | [], o, ne, T, ho, hne, h => by
    refine ⟨?_, fun c hc => absurd hc List.not_mem_nil⟩
    obtain ⟨R1, e1, h1⟩ := emitIf_true (k := fun T => emitIf ne 0 T fun T =>
      List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) T) h
    obtain ⟨R2, e2, h2⟩ := emitIf_true h1
    have e3 : R2 = [] := by
      cases R2 with
      | nil => rfl
      | cons _ _ => exact absurd h2 Bool.false_ne_true
    unfold rest
    rw [List.splitOnP_nil]
    dsimp only
    rw [e1, e2, e3]
    simp only [List.append_nil, toks_digits ho, List.isEmpty_nil, Bool.not_true, Bool.or_false,
      List.filter_nil, List.map_nil, encodeL_nil]
    cases hn : ne
    · have ho' : o = [] := by
        by_contra h'
        rw [hne h'] at hn
        exact Bool.noConfusion hn
      subst ho'
      rfl
    · cases ho2 : o.isEmpty <;> simp
  | ch :: d, o, ne, T, ho, hne, h => by
    rw [run_data] at h
    split_ifs at h with h10 h32 hdig
    ·
      obtain rfl := lf_of h10
      obtain ⟨R1, e1, h1⟩ := emitIf_true h
      obtain ⟨R2, e2, h2⟩ := emitIf_true h1
      obtain ⟨e3, hc⟩ := run_data_sound d [] false R2 (by simp) (by simp) (by rw [val_nil]; exact h2)
      refine ⟨?_, fun c hc' => ?_⟩
      · rw [e1, e2, e3, rest_lf, rest_init, toks_digits ho]
        cases hn : ne
        · have ho' : o = [] := by
            by_contra h'
            rw [hne h'] at hn
            exact Bool.noConfusion hn
          subst ho'
          rfl
        · cases ho2 : o.isEmpty <;> simp
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inr (Or.inr rfl)
        · exact hc c hc'
    ·
      obtain rfl := sp_of h32
      obtain ⟨R1, e1, h1⟩ := emitIf_true h
      obtain ⟨e3, hc⟩ := run_data_sound d [] true R1 (by simp) (by simp) (by rw [val_nil]; exact h1)
      refine ⟨?_, fun c hc' => ?_⟩
      · rw [e1, e3]
        unfold rest
        obtain ⟨r, ls, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') d)
        rw [List.splitOnP_cons_eq_ite_modifyHead,
          ite_eq_right (show ¬ ((' ' == '\n') = true) by decide), e, List.modifyHead_cons]
        dsimp only
        rw [toks_space ho]
        cases ho2 : o.isEmpty <;> simp
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact Or.inr (Or.inl rfl)
        · exact hc c hc'
    ·
      have hd : ch.isDigit = true := CFSG.KS.SporSch.LyTxt.isDigit_of hdig
      have ho' : ∀ c ∈ o ++ [ch], c.isDigit = true := by
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact ho c hc
        · rw [List.mem_singleton.1 hc]
          exact hd
      have e : val o * 10 + (ch.toNat - 48) = val (o ++ [ch]) :=
        (CFSG.KS.SporSch.LyTxt.ofDigitChars_snoc o ch).symm
      have e2 : (!(o ++ [ch]).isEmpty) = true := by simp
      have h' : run d false (val (o ++ [ch])) (!(o ++ [ch]).isEmpty) true T = true := by
        rw [e2, ← e]
        exact h
      obtain ⟨e3, hc⟩ := run_data_sound d (o ++ [ch]) true T ho' (fun _ => rfl) h'
      refine ⟨by rw [e3, rest_cons_ne (ne_lf h10)], fun c hc' => ?_⟩
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact Or.inl hd
      · exact hc c hc'

theorem run_header : ∀ (cs : List Char) (ne : Bool) (T : List Nat),
    run cs true 0 false ne T = true →
    ∃ h d, cs = h ++ '\n' :: d ∧ (ne = true ∨ h ≠ []) ∧ (∀ c ∈ h, (c == '\n') = false) ∧
      run d false 0 false false T = true
  | [], ne, T, h => absurd h Bool.false_ne_true
  | ch :: cs, ne, T, h => by
    rw [run_head] at h
    by_cases h10 : Nat.beq ch.toNat 10 = true
    · rw [ite_eq_left h10] at h
      obtain rfl := lf_of h10
      rw [Bool.and_eq_true] at h
      exact ⟨[], cs, rfl, Or.inl h.1, fun c hc => absurd hc List.not_mem_nil, h.2⟩
    · rw [ite_eq_right h10] at h
      obtain ⟨hh, d, e, -, hn, hr⟩ := run_header cs true T h
      refine ⟨ch :: hh, d, by rw [e]; rfl, Or.inr (List.cons_ne_nil _ _), fun c hc => ?_, hr⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ne_lf h10
      · exact hn c hc

theorem linesOf_of_chk {cs : List Char} {E : List (List Nat)} (h : linesChk cs (encodeL E) = true) :
    linesOf (String.ofList cs) = (E.map List.toArray).toArray := by
  obtain ⟨hh, d, rfl, hne, hnl, hr⟩ := run_header cs false (encodeL E) h
  have hne' : hh ≠ [] := hne.resolve_left (by decide)
  obtain ⟨hT, hch⟩ := run_data_sound d [] false (encodeL E) (by simp) (by simp)
    (by rw [val_nil]; exact hr)
  rw [rest_init] at hT
  obtain rfl := encodeL_inj _ _ hT
  unfold linesOf dataLines
  rw [textLines_ofList, List.splitOnP_append_cons_of_forall_mem (p := (· == '\n')) hnl '\n' rfl d,
    List.filter_cons_of_pos (by simpa using hne'), List.map_cons, List.drop_one, List.tail_cons,
    List.map_map]
  unfold lns
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hl' : l ∈ d.splitOnP (· == '\n') := (List.mem_filter.1 hl).1
  simp only [Function.comp]
  refine parseNats_ofList fun c hc => ?_
  obtain ⟨h1, h2⟩ := mem_splitOnP d l hl' c hc
  rcases hch c h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · subst h
    exact absurd h2 (by decide)

end CFSG.KS.DecLines

end
