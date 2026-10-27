module

public import Certificates.Data.Kernel.Spor.DecSL
public import CFSG.Sporadic.ONOddCore.LocalAutPayload
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
public import Std.Data.DTreeMap.Internal.Balancing

namespace CFSG.KS.DecSL

open CFSG.KS.DecLines CFSG.KS.SporSch.LyTxt

def sepC (c : Char) : Bool := c == ' ' || c == '\n'

def toksS (l : List Char) : List Nat :=
  ((l.splitOnP sepC).filter fun p => !p.isEmpty).map val

theorem sepC_of_digit {c : Char} (h : c.isDigit = true) : sepC c = false := by
  have h1 : c ≠ ' ' := by
    rintro rfl
    exact absurd h (by decide)
  have h2 : c ≠ '\n' := by
    rintro rfl
    exact absurd h (by decide)
  simp [sepC, h1, h2]

theorem toksS_digits {o : List Char} (ho : ∀ c ∈ o, c.isDigit = true) :
    toksS o = if o.isEmpty then [] else [val o] := by
  unfold toksS
  rw [List.splitOnP_eq_singleton (p := sepC) fun x hx => sepC_of_digit (ho x hx)]
  cases o <;> rfl

theorem toksS_sep {o : List Char} (ho : ∀ c ∈ o, c.isDigit = true) {s : Char} (hs : sepC s = true)
    (r : List Char) : toksS (o ++ s :: r) = (if o.isEmpty then [] else [val o]) ++ toksS r := by
  unfold toksS
  rw [List.splitOnP_append_cons_of_forall_mem (p := sepC) (fun x hx => sepC_of_digit (ho x hx)) s
    hs r]
  cases o <;> rfl

theorem flatMap_split : ∀ xs : List Char,
    (xs.splitOnP (· == '\n')).flatMap (·.splitOnP (· == ' ')) = xs.splitOnP sepC
  | [] => by simp [List.splitOnP_nil]
  | x :: xs => by
    rw [List.splitOnP_cons_eq_ite_modifyHead, List.splitOnP_cons_eq_ite_modifyHead]
    by_cases hn : (x == '\n') = true
    · have hs : sepC x = true := by simp [sepC, hn]
      rw [ite_eq_left hn, ite_eq_left hs, List.flatMap_cons, flatMap_split xs, List.splitOnP_nil]
      rfl
    · obtain ⟨h, t, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') xs)
      have ih := flatMap_split xs
      rw [e, List.flatMap_cons] at ih
      rw [ite_eq_right hn, e, List.modifyHead_cons, List.flatMap_cons,
        List.splitOnP_cons_eq_ite_modifyHead]
      by_cases hs : (x == ' ') = true
      · have hs' : sepC x = true := by simp [sepC, hs]
        rw [ite_eq_left hs, ite_eq_left hs', ← ih]
        rfl
      · have hs' : ¬ sepC x = true := by simp_all [sepC]
        rw [ite_eq_right hs, ite_eq_right hs', ← ih]
        obtain ⟨a, b, e2⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == ' ') h)
        rw [e2, List.cons_append, List.modifyHead_cons, List.modifyHead_cons, List.cons_append]

theorem isSep_cases {c : Char} (h : isSep c.toNat = true) : c = ' ' ∨ c = '\n' := by
  unfold isSep at h
  cases h32 : Nat.beq c.toNat 32
  · rw [h32] at h
    exact Or.inr ((char_of_beq h (by decide)).trans (by decide))
  · exact Or.inl ((char_of_beq h32 (by decide)).trans (by decide))

theorem digitsSLOK_cons (ch : Char) (cs : List Char) :
    digitsSLOK (ch :: cs) = ((Bool.rec (motive := fun _ => Bool)
      (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) true (isSep ch.toNat)) && digitsSLOK cs) := by
  have e : digitsSLOK (ch :: cs) = Bool.rec (motive := fun _ => Bool) false (digitsSLOK cs)
      (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
        (Nat.ble ch.toNat 57) (Nat.ble 48 ch.toNat)) true (isSep ch.toNat)) := rfl
  rw [e, bAnd_eqT, bAnd_eqT]

theorem digitsSLOK_mem : ∀ {cs : List Char}, digitsSLOK cs = true →
    ∀ c ∈ cs, sepC c = true ∨ c.isDigit = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | ch :: cs, h, c, hc => by
    rw [digitsSLOK_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · cases hs : isSep c.toNat
      · rw [hs] at h
        exact Or.inr (isDigit_of h.1)
      · rcases isSep_cases hs with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inl rfl
    · exact digitsSLOK_mem h.2 c hc

theorem natsRun_nil (cur : Nat) (st : Bool) : natsRun [] cur st = if st then [cur] else [] := by
  cases st <;> rfl

theorem natsRun_cons (ch : Char) (cs : List Char) (cur : Nat) (st : Bool) :
    natsRun (ch :: cs) cur st = if isSep ch.toNat = true then
      (if st then cur :: natsRun cs 0 false else natsRun cs 0 false)
      else natsRun cs (cur * 10 + (ch.toNat - 48)) true := by
  have e : natsRun (ch :: cs) cur st = Bool.rec (motive := fun _ => List Nat)
      (natsRun cs (Nat.add (Nat.mul cur 10) (Nat.sub ch.toNat 48)) true)
      (Bool.rec (motive := fun _ => List Nat) (natsRun cs 0 false)
        (List.cons cur (natsRun cs 0 false)) st) (isSep ch.toNat) := rfl
  rw [e]
  generalize isSep ch.toNat = b
  cases b <;> cases st <;> rfl

theorem run_toks : ∀ (cs o : List Char), digitsSLOK cs = true → (∀ c ∈ o, c.isDigit = true) →
    natsRun cs (val o) (!o.isEmpty) = toksS (o ++ cs)
  | [], o, _, ho => by
    rw [natsRun_nil, List.append_nil, toksS_digits ho]
    cases o <;> rfl
  | ch :: cs, o, h, ho => by
    have hd := h
    rw [digitsSLOK_cons, Bool.and_eq_true] at hd
    rw [natsRun_cons]
    by_cases hs : isSep ch.toNat = true
    · have hsc : sepC ch = true := by
        rcases isSep_cases hs with rfl | rfl
        · rfl
        · rfl
      have hr := run_toks cs [] hd.2 (by simp)
      rw [List.nil_append, val_nil] at hr
      rw [ite_eq_left hs, toksS_sep ho hsc cs, ← hr]
      cases o <;> rfl
    · rw [ite_eq_right hs]
      have hs' : isSep ch.toNat = false := by simpa using hs
      rw [hs'] at hd
      have hdig : ch.isDigit = true := isDigit_of hd.1
      have ho' : ∀ c ∈ o ++ [ch], c.isDigit = true := by
        intro c hc
        rcases List.mem_append.1 hc with hc | hc
        · exact ho c hc
        · rw [List.mem_singleton.1 hc]
          exact hdig
      have e : o ++ ch :: cs = (o ++ [ch]) ++ cs := by simp
      rw [e, ← run_toks cs (o ++ [ch]) hd.2 ho']
      have hv : val (o ++ [ch]) = val o * 10 + (ch.toNat - 48) := ofDigitChars_snoc o ch
      have hne : (o ++ [ch]).isEmpty = false := by simp
      rw [hv, hne]
      rfl

public theorem natsOf_ofList_proved {cs : List Char} (h : digitsSLOK cs = true) :
    CFSG.Sporadic.ONOddCore.natsOf (String.ofList cs) = natsSL cs := by
  have hr := run_toks cs [] h (by simp)
  rw [List.nil_append, val_nil, List.isEmpty_nil, Bool.not_true] at hr
  unfold CFSG.Sporadic.ONOddCore.natsOf natsSL
  rw [hr, splitOn_nl, List.splitOnPPrepend_nil_right, List.flatMap_map]
  simp only [splitOn_sp, List.splitOnPPrepend_nil_right]
  rw [← List.map_flatMap, flatMap_split, List.filter_map, List.map_map]
  unfold toksS
  have hf : (cs.splitOnP sepC).filter ((fun w : String => !w.isEmpty) ∘ String.ofList) =
      (cs.splitOnP sepC).filter fun p => !p.isEmpty :=
    List.filter_congr fun q _ => by simp only [Function.comp_apply, ofList_isEmpty]
  rw [hf]
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
  have hdq : ∀ c ∈ q, c.isDigit = true := by
    intro c hc
    obtain ⟨h1, h2⟩ := mem_splitOnP cs q hq1 c hc
    rcases digitsSLOK_mem h c h1 with h3 | h3
    · rw [h2] at h3
      exact absurd h3 Bool.false_ne_true
    · exact h3
  exact toNat!_of (toNat_digits hdq (by simpa using hq2))

end CFSG.KS.DecSL
