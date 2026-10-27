module

public import Certificates.Data.Kernel.Spor.DecLinesI
public import CFSG.Sporadic.HNOddCore.InvArrays
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Mathlib.Tactic.SplitIfs

public section

namespace CFSG.KS.DecLines

open CFSG.Sporadic.HNOddCore.InvData CFSG.YGroups.ModelNative

private def toksI (l : List Char) : List Int :=
  ((l.splitOnP (· == ' ')).filter fun p => !p.isEmpty).map fun p => (String.ofList p).toInt!

private def lnsI (d : List Char) : List (List Int) :=
  ((d.splitOnP (· == '\n')).filter fun l => !l.isEmpty).map toksI

private def sg (neg : Bool) : List Char := if neg = true then ['-'] else []

private theorem toInt!_of' {s : String} {v : Int} (h : s.toInt? = some v) : s.toInt! = v := by
  unfold String.toInt? at h
  unfold String.toInt! String.Slice.toInt!
  rw [h]

private theorem toInt!_digits {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    (String.ofList ds).toInt! = (val ds : Int) :=
  toInt!_of' (CFSG.KS.SporSch.LyTxt.tv_pos hd hne)

private theorem toInt!_neg {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    (String.ofList ('-' :: ds)).toInt! = -(val ds : Int) :=
  toInt!_of' (CFSG.KS.SporSch.LyTxt.tv_neg hd hne)

private theorem tokI_ofNat' (a : Nat) : tokI (Int.ofNat a) = 2 * a + 1 := rfl

private theorem tokI_negSucc (b : Nat) : tokI (Int.negSucc b) = 2 * b + 2 := rfl

private theorem tokI_natCast (n : Nat) : tokI (n : Int) = Nat.succ (Nat.mul 2 n) := rfl

private theorem tokI_neg {n : Nat} (hn : 0 < n) : tokI (-(n : Int)) = Nat.mul 2 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e : -(((m + 1 : Nat)) : Int) = Int.negSucc m := rfl
  rw [e, tokI_negSucc]
  show 2 * m + 2 = 2 * (m + 1)
  omega

private theorem tokI_inj {a b : Int} (h : tokI a = tokI b) : a = b := by
  cases a with
  | ofNat a =>
    cases b with
    | ofNat b =>
      rw [tokI_ofNat', tokI_ofNat'] at h
      congr 1
      omega
    | negSucc b =>
      rw [tokI_ofNat', tokI_negSucc] at h
      omega
  | negSucc a =>
    cases b with
    | ofNat b =>
      rw [tokI_negSucc, tokI_ofNat'] at h
      omega
    | negSucc b =>
      rw [tokI_negSucc, tokI_negSucc] at h
      congr 1
      omega

private theorem tokI_ne_zero (a : Int) : tokI a ≠ 0 := by
  cases a with
  | ofNat a =>
    rw [tokI_ofNat']
    omega
  | negSucc a =>
    rw [tokI_negSucc]
    omega

private theorem encodeLI_nil : encodeLI [] = [] := rfl

private theorem encodeLI_cons (l : List Int) (E : List (List Int)) :
    encodeLI (l :: E) = l.map tokI ++ 0 :: encodeLI E := by
  change List.rec (motive := fun _ => List Nat) (List.cons 0 (encodeLI E))
    (fun x _ ih2 => List.cons (tokI x) ih2) l = _
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (List.cons (tokI x)) ih

private theorem prefix_injI : ∀ (l l' : List Int) (X X' : List Nat),
    l.map tokI ++ 0 :: X = l'.map tokI ++ 0 :: X' → l = l' ∧ X = X'
  | [], [], X, X', h => ⟨rfl, by simpa using h⟩
  | [], b :: l', X, X', h => by
    rw [List.map_nil, List.nil_append, List.map_cons, List.cons_append] at h
    exact absurd (List.cons.inj h).1.symm (tokI_ne_zero b)
  | a :: l, [], X, X', h => by
    rw [List.map_nil, List.nil_append, List.map_cons, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (tokI_ne_zero a)
  | a :: l, b :: l', X, X', h => by
    rw [List.map_cons, List.map_cons, List.cons_append, List.cons_append] at h
    obtain ⟨hab, h⟩ := List.cons.inj h
    obtain ⟨rfl, rfl⟩ := prefix_injI l l' X X' h
    exact ⟨by rw [tokI_inj hab], rfl⟩

private theorem encodeLI_inj : ∀ (E E' : List (List Int)), encodeLI E = encodeLI E' → E = E'
  | [], [], _ => rfl
  | [], l :: E', h => by rw [encodeLI_nil, encodeLI_cons] at h; simp at h
  | l :: E, [], h => by rw [encodeLI_nil, encodeLI_cons] at h; simp at h
  | l :: E, l' :: E', h => by
    rw [encodeLI_cons, encodeLI_cons] at h
    obtain ⟨rfl, h2⟩ := prefix_injI _ _ _ _ h
    rw [encodeLI_inj E E' h2]

private theorem toksI_word {o : List Char} (ho : ∀ c ∈ o, (c == ' ') = false) :
    toksI o = if o.isEmpty then [] else [(String.ofList o).toInt!] := by
  unfold toksI
  rw [List.splitOnP_eq_singleton (p := (· == ' ')) ho]
  cases o <;> rfl

private theorem toksI_nil : toksI [] = [] := by
  unfold toksI
  simp

private theorem toksI_space {o : List Char} (ho : ∀ c ∈ o, (c == ' ') = false) (r : List Char) :
    toksI (o ++ ' ' :: r) = toksI o ++ toksI r := by
  rw [toksI_word ho]
  unfold toksI
  rw [List.splitOnP_append_cons_of_forall_mem (p := (· == ' ')) ho ' ' rfl r]
  cases o <;> rfl

private theorem filterMap_pieces : ∀ (ps : List (List Char)),
    (ps.map String.ofList).filterMap (fun t => if t.isEmpty then none else some t.toInt!) =
      (ps.filter fun p => !p.isEmpty).map fun p => (String.ofList p).toInt!
  | [] => rfl
  | p :: ps => by
    have e : (fun t : String => if t.isEmpty then none else some t.toInt!) (String.ofList p) =
        if p.isEmpty then none else some (String.ofList p).toInt! := by
      dsimp only
      rw [ofList_isEmpty]
    rw [List.map_cons]
    by_cases hp : p.isEmpty = true
    · rw [if_pos hp] at e
      rw [List.filterMap_cons_none (f := fun t : String => if t.isEmpty then none else some t.toInt!)
        (a := String.ofList p) e, filterMap_pieces ps, List.filter_cons_of_neg (by simp [hp])]
    · rw [if_neg hp] at e
      rw [List.filterMap_cons_some (f := fun t : String => if t.isEmpty then none else some t.toInt!)
        (a := String.ofList p) e, filterMap_pieces ps,
        List.filter_cons_of_pos (by simpa using hp), List.map_cons]

private theorem parseInts_ofList' (l : List Char) : parseInts (String.ofList l) = toksI l := by
  unfold parseInts toksI
  rw [CFSG.KS.SporSch.LyTxt.splitOn_sp, List.splitOnPPrepend_nil_right, filterMap_pieces]

private noncomputable def restI (d o : List Char) (ne : Bool) : List Nat :=
  match d.splitOnP (· == '\n') with
  | [] => []
  | r :: ls => (if (ne || !r.isEmpty) = true then (toksI (o ++ r)).map tokI ++ [0] else []) ++
      encodeLI ((ls.filter fun l => !l.isEmpty).map toksI)

private theorem restI_init (d : List Char) : restI d [] false = encodeLI (lnsI d) := by
  unfold restI lnsI
  obtain ⟨r, ls, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') d)
  rw [e]
  dsimp only
  cases hr : r.isEmpty
  · rw [List.filter_cons_of_pos (by simp [hr]), List.map_cons, encodeLI_cons]
    simp
  · rw [List.filter_cons_of_neg (by simp [hr])]
    simp

private theorem restI_cons_ne {ch : Char} (h : (ch == '\n') = false) (d o : List Char)
    (ne : Bool) : restI (ch :: d) o ne = restI d (o ++ [ch]) true := by
  unfold restI
  obtain ⟨r, ls, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') d)
  rw [List.splitOnP_cons_eq_ite_modifyHead, if_neg (by simp [h]), e, List.modifyHead_cons]
  simp

private theorem restI_lf (d o : List Char) (ne : Bool) :
    restI ('\n' :: d) o ne = (if ne = true then (toksI o).map tokI ++ [0] else []) ++
      encodeLI (lnsI d) := by
  unfold restI
  rw [List.splitOnP_cons_eq_ite_modifyHead, if_pos (by decide : ('\n' == '\n') = true)]
  simp only [List.isEmpty_nil, Bool.not_true, Bool.or_false, List.append_nil, lnsI]

private theorem sg_ne_sp (neg : Bool) {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) :
    ∀ c ∈ sg neg ++ ds, (c == ' ') = false := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · cases neg
    · simp [sg] at hc
    · simp only [sg, if_true, List.mem_singleton] at hc
      subst hc
      rfl
  · have h := hd c hc
    cases e : (c == ' ')
    · rfl
    · rw [beq_iff_eq] at e
      subst e
      exact absurd h (by decide)

private theorem open_nil {neg : Bool} {ds : List Char} {ne : Bool}
    (hne : (neg = true ∨ ds ≠ []) → ne = true) (hn : ne = false) : sg neg ++ ds = [] := by
  cases neg
  · cases ds with
    | nil => rfl
    | cons c ds' => exact absurd (hne (Or.inr (List.cons_ne_nil _ _))) (by rw [hn]; decide)
  · exact absurd (hne (Or.inl rfl)) (by rw [hn]; decide)

private theorem endI_true {neg : Bool} {ds : List Char} {T : List Nat} {k : List Nat → Bool}
    (hd : ∀ c ∈ ds, c.isDigit = true) (h : endI (!ds.isEmpty) neg (val ds) T k = true) :
    ∃ R, T = (toksI (sg neg ++ ds)).map tokI ++ R ∧ k R = true := by
  rw [toksI_word (sg_ne_sp neg hd)]
  cases ds with
  | nil =>
    cases neg
    · exact ⟨T, rfl, h⟩
    · have e : endI (!([] : List Char).isEmpty) true (val []) T k = false := rfl
      rw [e] at h
      exact absurd h Bool.false_ne_true
  | cons c ds' =>
    have hne : c :: ds' ≠ [] := List.cons_ne_nil _ _
    cases neg
    · have h' : emit (Nat.succ (Nat.mul 2 (val (c :: ds')))) T k = true := h
      obtain ⟨R, rfl, hk⟩ := emit_true h'
      refine ⟨R, ?_, hk⟩
      have e1 : sg false ++ c :: ds' = c :: ds' := rfl
      rw [e1, if_neg (by simp), toInt!_digits hd hne, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, tokI_natCast]
    · have h' : Bool.rec (motive := fun _ => Bool) false (emit (Nat.mul 2 (val (c :: ds'))) T k)
          (Nat.blt 0 (val (c :: ds'))) = true := h
      obtain ⟨h0, h1⟩ := band_true h'
      obtain ⟨R, rfl, hk⟩ := emit_true h1
      refine ⟨R, ?_, hk⟩
      have e1 : sg true ++ c :: ds' = '-' :: c :: ds' := rfl
      rw [e1, if_neg (by simp), toInt!_neg hd hne, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, tokI_neg (Nat.blt_eq.mp h0)]

private theorem runI_data (ch : Char) (cs : List Char) (cur : Nat) (num neg ne : Bool)
    (T : List Nat) :
    runI (ch :: cs) false cur num neg ne T =
      if Nat.beq ch.toNat 10 = true then
        endI num neg cur T fun T => emitIf ne 0 T fun T => runI cs false 0 false false false T
      else if Nat.beq ch.toNat 32 = true then
        endI num neg cur T fun T => runI cs false 0 false false true T
      else if Nat.beq ch.toNat 45 = true then
        ((!num && !neg) && runI cs false 0 false true true T)
      else if (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = true then
        runI cs false (cur * 10 + (ch.toNat - 48)) true neg true T
      else false := by
  change Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (runI cs false (Nat.add (Nat.mul cur 10) (Nat.sub ch.toNat 48)) true neg true T)
          (Bool.rec (motive := fun _ => Bool) false (Nat.ble ch.toNat 57) (Nat.ble 48 ch.toNat)))
        (Bool.rec (motive := fun _ => Bool) false (runI cs false 0 false true true T)
          (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false neg)
            false num))
        (Nat.beq ch.toNat 45))
      (endI num neg cur T fun T => runI cs false 0 false false true T)
      (Nat.beq ch.toNat 32))
    (endI num neg cur T fun T => emitIf ne 0 T fun T => runI cs false 0 false false false T)
    (Nat.beq ch.toNat 10) = _
  cases Nat.beq ch.toNat 10 <;> cases Nat.beq ch.toNat 32 <;> cases Nat.beq ch.toNat 45 <;>
    cases Nat.ble 48 ch.toNat <;> cases Nat.ble ch.toNat 57 <;> cases num <;> cases neg <;> rfl

private theorem runI_head (ch : Char) (cs : List Char) (ne : Bool) (T : List Nat) :
    runI (ch :: cs) true 0 false false ne T =
      if Nat.beq ch.toNat 10 = true then (ne && runI cs false 0 false false false T)
      else runI cs true 0 false false true T := by
  change Bool.rec (motive := fun _ => Bool) (runI cs true 0 false false true T)
    (Bool.rec (motive := fun _ => Bool) false (runI cs false 0 false false false T) ne)
    (Nat.beq ch.toNat 10) = _
  cases Nat.beq ch.toNat 10 <;> cases ne <;> rfl

private theorem runI_data_sound : ∀ (d : List Char) (neg : Bool) (ds : List Char) (ne : Bool)
    (T : List Nat), (∀ c ∈ ds, c.isDigit = true) → ((neg = true ∨ ds ≠ []) → ne = true) →
    runI d false (val ds) (!ds.isEmpty) neg ne T = true → T = restI d (sg neg ++ ds) ne
  | [], neg, ds, ne, T, hd, hne, h => by
    obtain ⟨R1, e1, h1⟩ := endI_true (k := fun T => emitIf ne 0 T fun T =>
      List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) T) hd h
    obtain ⟨R2, e2, h2⟩ := emitIf_true h1
    have e3 : R2 = [] := by
      cases R2 with
      | nil => rfl
      | cons _ _ => exact absurd h2 Bool.false_ne_true
    unfold restI
    rw [List.splitOnP_nil]
    dsimp only
    rw [e1, e2, e3]
    simp only [List.append_nil, List.isEmpty_nil, Bool.not_true, Bool.or_false,
      List.filter_nil, List.map_nil, encodeLI_nil]
    cases hn : ne
    · rw [open_nil hne hn, toksI_nil]
      simp
    · simp
  | ch :: d, neg, ds, ne, T, hd, hne, h => by
    rw [runI_data] at h
    split_ifs at h with h10 h32 h45 hdig
    ·
      obtain rfl := lf_of h10
      obtain ⟨R1, e1, h1⟩ := endI_true hd h
      obtain ⟨R2, e2, h2⟩ := emitIf_true h1
      have e3 := runI_data_sound d false [] false R2 (by simp) (by simp)
        (by rw [val_nil]; exact h2)
      rw [e1, e2, e3, restI_lf, show sg false ++ [] = ([] : List Char) from rfl, restI_init]
      cases hn : ne
      · rw [open_nil hne hn, toksI_nil]
        simp
      · simp
    ·
      obtain rfl := sp_of h32
      obtain ⟨R1, e1, h1⟩ := endI_true hd h
      have e3 := runI_data_sound d false [] true R1 (by simp) (by simp)
        (by rw [val_nil]; exact h1)
      rw [e1, e3, show sg false ++ [] = ([] : List Char) from rfl]
      unfold restI
      obtain ⟨r, ls, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') d)
      rw [List.splitOnP_cons_eq_ite_modifyHead,
        if_neg (show ¬ ((' ' == '\n') = true) by decide), e, List.modifyHead_cons]
      dsimp only
      rw [toksI_space (sg_ne_sp neg hd)]
      simp
    ·
      obtain rfl : ch = '-' := CFSG.KS.SporSch.LyTxt.char_of_beq h45 (by decide)
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hnum, hneg⟩, h⟩ := h
      have hds : ds = [] := by simpa using hnum
      have hneg' : neg = false := by simpa using hneg
      subst hds hneg'
      have e3 := runI_data_sound d true [] true T (by simp) (by simp) (by rw [val_nil]; exact h)
      rw [e3, restI_cons_ne (by decide : ('-' == '\n') = false)]
      rfl
    ·
      have hdc : ch.isDigit = true := CFSG.KS.SporSch.LyTxt.isDigit_of hdig
      have hd' : ∀ c ∈ ds ++ [ch], c.isDigit = true := by
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact hd c hc
        · rw [List.mem_singleton.1 hc]
          exact hdc
      have e : val ds * 10 + (ch.toNat - 48) = val (ds ++ [ch]) :=
        (CFSG.KS.SporSch.LyTxt.ofDigitChars_snoc ds ch).symm
      have e2 : (!(ds ++ [ch]).isEmpty) = true := by simp
      have h' : runI d false (val (ds ++ [ch])) (!(ds ++ [ch]).isEmpty) neg true T = true := by
        rw [e2, ← e]
        exact h
      have e3 := runI_data_sound d neg (ds ++ [ch]) true T hd' (fun _ => rfl) h'
      rw [e3, restI_cons_ne (ne_lf h10), List.append_assoc]

private theorem runI_header : ∀ (cs : List Char) (ne : Bool) (T : List Nat),
    runI cs true 0 false false ne T = true →
    ∃ h d, cs = h ++ '\n' :: d ∧ (ne = true ∨ h ≠ []) ∧ (∀ c ∈ h, (c == '\n') = false) ∧
      runI d false 0 false false false T = true
  | [], ne, T, h => absurd h Bool.false_ne_true
  | ch :: cs, ne, T, h => by
    rw [runI_head] at h
    by_cases h10 : Nat.beq ch.toNat 10 = true
    · rw [if_pos h10] at h
      obtain rfl := lf_of h10
      rw [Bool.and_eq_true] at h
      exact ⟨[], cs, rfl, Or.inl h.1, fun c hc => absurd hc List.not_mem_nil, h.2⟩
    · rw [if_neg h10] at h
      obtain ⟨hh, d, e, -, hn, hr⟩ := runI_header cs true T h
      refine ⟨ch :: hh, d, by rw [e]; rfl, Or.inr (List.cons_ne_nil _ _), fun c hc => ?_, hr⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ne_lf h10
      · exact hn c hc

theorem intLinesOf_ofList {cs : List Char} {E : List (List Int)}
    (h : linesChkI cs (encodeLI E) = true) :
    CFSG.Sporadic.HNOddCore.InvData.intLinesOf (String.ofList cs) = E.toArray := by
  obtain ⟨hh, d, rfl, hne, hnl, hr⟩ := runI_header cs false (encodeLI E) h
  have hne' : hh ≠ [] := hne.resolve_left (by decide)
  have hT := runI_data_sound d false [] false (encodeLI E) (by simp) (by simp)
    (by rw [val_nil]; exact hr)
  rw [show sg false ++ [] = ([] : List Char) from rfl, restI_init] at hT
  obtain rfl := encodeLI_inj _ _ hT
  unfold intLinesOf dataLines
  rw [textLines_ofList, List.splitOnP_append_cons_of_forall_mem (p := (· == '\n')) hnl '\n' rfl d,
    List.filter_cons_of_pos (by simpa using hne'), List.map_cons, List.drop_one, List.tail_cons,
    List.map_map]
  unfold lnsI
  congr 1
  apply List.map_congr_left
  intro l _
  exact parseInts_ofList' l

end CFSG.KS.DecLines

end
