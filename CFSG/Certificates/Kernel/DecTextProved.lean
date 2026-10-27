module

public import Certificates.Data.Kernel.DecText
public import Certificates.Data.CFSGNative.Fi23.CentralizerData
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

namespace CFSG.KC.DecText

open CFSG.KS.DecLines CFSG.KS.SporSch.LyTxt

theorem digitsOK_cons (ch : Char) (cs : List Char) :
    digitsOK (ch :: cs) = ((Nat.beq ch.toNat 32 || (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57)) &&
      digitsOK cs) := rfl

theorem natsRun_nil (cur : Nat) (st : Bool) : natsRun [] cur st = if st then [cur] else [] := by
  cases st <;> rfl

theorem natsRun_cons (ch : Char) (cs : List Char) (cur : Nat) (st : Bool) :
    natsRun (ch :: cs) cur st = if Nat.beq ch.toNat 32 = true then
      (if st then cur :: natsRun cs 0 false else natsRun cs 0 false)
      else natsRun cs (cur * 10 + (ch.toNat - 48)) true := by
  have e : natsRun (ch :: cs) cur st = Bool.rec (motive := fun _ => List Nat)
      (natsRun cs (Nat.add (Nat.mul cur 10) (Nat.sub ch.toNat 48)) true)
      (Bool.rec (motive := fun _ => List Nat) (natsRun cs 0 false)
        (List.cons cur (natsRun cs 0 false)) st) (Nat.beq ch.toNat 32) := rfl
  rw [e]
  generalize Nat.beq ch.toNat 32 = b
  cases b <;> cases st <;> rfl

theorem digitsOK_mem : ∀ {cs : List Char}, digitsOK cs = true → ∀ c ∈ cs, c = ' ' ∨ c.isDigit = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | ch :: cs, h, c, hc => by
    rw [digitsOK_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · by_cases hs : Nat.beq c.toNat 32 = true
      · exact Or.inl ((char_of_beq hs (by decide)).trans (by decide))
      · exact Or.inr (isDigit_of (by simpa [hs] using h.1))
    · exact digitsOK_mem h.2 c hc

theorem run_toks : ∀ (cs o : List Char), digitsOK cs = true → (∀ c ∈ o, c.isDigit = true) →
    natsRun cs (val o) (!o.isEmpty) = toks (o ++ cs)
  | [], o, _, ho => by
    rw [natsRun_nil, List.append_nil, toks_digits ho]
    cases o <;> rfl
  | ch :: cs, o, h, ho => by
    have hd := h
    rw [digitsOK_cons, Bool.and_eq_true] at hd
    rw [natsRun_cons]
    by_cases hs : Nat.beq ch.toNat 32 = true
    · have hch : ch = ' ' := (char_of_beq hs (by decide)).trans (by decide)
      subst hch
      have hr := run_toks cs [] hd.2 (by simp)
      rw [List.nil_append, val_nil] at hr
      rw [ite_eq_left hs, toks_space ho cs, ← hr]
      cases o <;> rfl
    · rw [ite_eq_right hs]
      have hdig : ch.isDigit = true := isDigit_of (by simpa [hs] using hd.1)
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

theorem bne_empty (q : List Char) : (String.ofList q != "") = !q.isEmpty := by
  rw [Bool.eq_iff_iff]
  simp [bne_iff_ne, String.ofList_eq_empty_iff]

public theorem natsOf_ofList_proved {cs : List Char} (h : digitsOK cs = true) :
    CFSG.Sporadic.Fi23.Native.natsOf (String.ofList cs) = (natsK cs).toArray := by
  have hr := run_toks cs [] h (by simp)
  rw [List.nil_append] at hr
  unfold CFSG.Sporadic.Fi23.Native.natsOf natsK
  rw [splitOn_sp, List.splitOnPPrepend_nil_right, List.map_toArray]
  rw [val_nil, List.isEmpty_nil, Bool.not_true] at hr
  rw [hr]
  unfold toks
  congr 1
  rw [List.filter_map, List.map_map]
  have hf : (cs.splitOnP (· == ' ')).filter ((fun w => w != "") ∘ String.ofList) =
      (cs.splitOnP (· == ' ')).filter fun p => !p.isEmpty :=
    List.filter_congr fun q _ => by simp only [Function.comp_apply, bne_empty]
  rw [hf]
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
  have hdq : ∀ c ∈ q, c.isDigit = true := by
    intro c hc
    obtain ⟨h1, h2⟩ := mem_splitOnP cs q hq1 c hc
    rcases digitsOK_mem h c h1 with rfl | hc'
    · exact absurd h2 (by decide)
    · exact hc'
  exact toNat!_of (toNat_digits hdq (by simpa using hq2))

end CFSG.KC.DecText
