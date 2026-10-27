module

public import Certificates.Data.CFSGNative.Fi22.LocalData
public import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

public section

namespace CFSG.KS.WordInts

open CFSG.Sporadic.Fi22.Native CFSG.KS.SporSch.LyTxt

@[expose] def spl : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc => if c = ' ' then acc.reverse :: spl cs [] else spl cs (c :: acc)

theorem spl_eq (cs acc : List Char) : spl cs acc = List.splitOnPPrepend (· == ' ') cs acc := by
  induction cs generalizing acc with
  | nil => rw [spl, List.splitOnPPrepend_nil]
  | cons c cs ih =>
    rw [spl, List.splitOnPPrepend_cons_eq_ite, ih, ih]
    by_cases h : c = ' ' <;> simp [h]

@[expose] def dval : List Char → Nat → Nat
  | [], a => a
  | c :: cs, a => dval cs (10 * a + (c.toNat - 48))

theorem dval_eq (cs : List Char) (a : Nat) : dval cs a = Nat.ofDigitChars 10 cs a := by
  induction cs generalizing a with
  | nil => rw [dval, Nat.ofDigitChars_nil]
  | cons c cs ih =>
    rw [dval, Nat.ofDigitChars_cons, ih]
    rfl

@[expose] def digitsOK (ds : List Char) : Bool := !ds.isEmpty && ds.all fun c => c.isDigit

@[expose] def tokOK (p : List Char) : Bool :=
  if p.head? = some '-' then digitsOK p.tail else digitsOK p

@[expose] def tokVal (p : List Char) : Int :=
  if p.head? = some '-' then -(dval p.tail 0 : Int) else (dval p 0 : Int)

theorem digits_of {ds : List Char} (h : digitsOK ds = true) :
    (∀ c ∈ ds, c.isDigit = true) ∧ ds ≠ [] := by
  simp only [digitsOK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  exact ⟨h.2, h.1⟩

theorem tv_tok {p : List Char} (h : tokOK p = true) : (tv p).getD 0 = tokVal p := by
  unfold tokOK at h
  unfold tokVal
  by_cases hm : p.head? = some '-'
  · rw [ite_eq_left hm] at h ⊢
    obtain ⟨ds, rfl⟩ : ∃ ds, p = '-' :: ds := by
      cases p with
      | nil => simp at hm
      | cons c ds =>
        simp only [List.head?_cons, Option.some.injEq] at hm
        exact ⟨ds, by rw [hm]⟩
    simp only [List.tail_cons] at h ⊢
    obtain ⟨h1, h2⟩ := digits_of h
    rw [tv_neg h1 h2, dval_eq]
    rfl
  · rw [ite_eq_right hm] at h ⊢
    obtain ⟨h1, h2⟩ := digits_of h
    rw [tv_pos h1 h2, dval_eq]
    rfl

theorem wordOfInts_ofList (cs : List Char)
    (h : ((spl cs []).all fun p => p.isEmpty || tokOK p) = true) :
    wordOfInts (String.ofList cs) = ((spl cs []).filter (fun p => !p.isEmpty)).map tokVal := by
  unfold wordOfInts
  rw [splitOn_sp, ← spl_eq, List.filter_map, List.map_map]
  have hf : ((fun x => x != "") ∘ String.ofList) = fun p : List Char => !p.isEmpty := by
    funext p
    cases p <;> simp
  rw [hf]
  apply List.map_congr_left
  intro p hp
  have hp' := List.mem_filter.1 hp
  have hq := List.all_eq_true.1 h p hp'.1
  have hne : p.isEmpty = false := by simpa using hp'.2
  rw [hne, Bool.false_or] at hq
  exact tv_tok hq

theorem wordOfInts_eq (s : String)
    (h : ((spl s.toList []).all fun p => p.isEmpty || tokOK p) = true) :
    wordOfInts s = ((spl s.toList []).filter (fun p => !p.isEmpty)).map tokVal := by
  have := wordOfInts_ofList s.toList h
  rwa [String.ofList_toList] at this

end CFSG.KS.WordInts

end
