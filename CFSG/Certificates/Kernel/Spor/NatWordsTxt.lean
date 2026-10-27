module

public import Certificates.Data.CFSGNative.Bridge.SurjD
public import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

public section

namespace CFSG.KS.NatWords

open CFSG.Sporadic.Bridge.SurjD.Native CFSG.KS.SporSch.LyTxt

@[expose] noncomputable def lines (cs : List Char) : List (List Char) :=
  (List.splitOnPPrepend (· == '\n') cs []).filter fun l => !l.isEmpty

@[expose] noncomputable def digitsOK (cs : List Char) : Bool :=
  (lines cs).all fun p => (List.splitOnP (· == ' ') p).all fun q =>
    q.all fun c => Nat.ble 48 c.toNat && Nat.ble c.toNat 57

@[expose] noncomputable def pieceVal (q : List Char) : Option Int :=
  if q.isEmpty then none else some ((Nat.ofDigitChars 10 q 0 : Nat) : Int)

@[expose] noncomputable def natWords (cs : List Char) : List (List Int) :=
  (lines cs).map fun p => (List.splitOnP (· == ' ') p).filterMap pieceVal

theorem tv_eq_pieceVal {q : List Char} (h : ∀ c ∈ q, c.isDigit = true) : tv q = pieceVal q := by
  cases q with
  | nil => rw [tv_nil]; rfl
  | cons c q => rw [tv_pos h (List.cons_ne_nil c q)]; rfl

theorem filterMap_tv : ∀ l : List (List Char), (∀ q ∈ l, ∀ c ∈ q, c.isDigit = true) →
    l.filterMap tv = l.filterMap pieceVal
  | [], _ => rfl
  | q :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, tv_eq_pieceVal (h q List.mem_cons_self),
      filterMap_tv l fun q' hq' => h q' (List.mem_cons_of_mem _ hq')]

theorem parseWords_ofList {cs : List Char} (h : digitsOK cs = true) :
    parseWords (String.ofList cs) = (natWords cs).toArray := by
  have hpl : ∀ p : List Char,
      parseLine (String.ofList p) = (List.splitOnP (· == ' ') p).filterMap tv := fun p => by
    unfold parseLine
    rw [splitOn_sp, List.filterMap_map, List.splitOnPPrepend_nil_right]
    rfl
  have hfl : ((String.ofList cs).splitOn "\n").filter (fun l => !l.isEmpty) =
      (lines cs).map String.ofList := by
    rw [splitOn_nl, List.filter_map, lines]
    congr 2
    funext p
    have hiso : (String.ofList p).isEmpty = p.isEmpty := by
      rw [Bool.eq_iff_iff, String.isEmpty_iff, List.isEmpty_iff, String.ofList_eq_empty_iff]
    change (!(String.ofList p).isEmpty) = !p.isEmpty
    rw [hiso]
  unfold parseWords natWords
  rw [hfl, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [Function.comp_apply, hpl]
  apply filterMap_tv
  intro q hq
  have h1 := List.all_eq_true.1 h p hp
  have h2 := List.all_eq_true.1 h1 q hq
  exact fun c hc => isDigit_of (List.all_eq_true.1 h2 c hc)

end CFSG.KS.NatWords

end
