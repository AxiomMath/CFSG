module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import CFSG.Certificates.Kernel.Common.StrSplit
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Data.String.ToNat

public section

namespace CFSG.KC.G2Three

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def pairOf (q : List Char) : Option (ℕ × ℕ) :=
  match q.splitOn ',' with
  | [a, b] => some (Nat.ofDigitChars 10 a 0, Nat.ofDigitChars 10 b 0)
  | _ => none

@[expose] def pieceOK (q : List Char) : Bool :=
  match q.splitOn ',' with
  | [a, b] => !a.isEmpty && !b.isEmpty && a.all Char.isDigit && b.all Char.isDigit
  | _ => false

@[expose] def piecesOK (cs : List Char) : Bool := (cs.splitOn ';').all pieceOK

theorem filter_digits' {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) :
    ds.filter (· != '_') = ds := by
  refine List.filter_eq_self.2 fun c hc => ?_
  have h := hd c hc
  have : c ≠ '_' := by
    rintro rfl
    exact absurd h (by decide)
  simpa using this

theorem toNat?_digits {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    (String.ofList ds).toNat? = some (Nat.ofDigitChars 10 ds 0) := by
  have hn : (String.ofList ds).isNat = true :=
    String.isNat_of_isDigit (by simpa using hne) (by simpa using hd)
  rw [String.toNat?_eq_some_ofDigitChars hn, String.toList_ofList, filter_digits' hd]

theorem semi_eq : (";" : String) = String.singleton ';' := by decide

theorem comma_eq : ("," : String) = String.singleton ',' := by decide

theorem piece_eq {q : List Char} (h : pieceOK q = true) :
    (match (String.ofList q).splitOn "," with
      | [a, b] => some (a.toNat?.getD 0, b.toNat?.getD 0)
      | _ => none) = pairOf q := by
  rw [comma_eq, CFSG.KC.Str.splitOn_ofList]
  unfold pieceOK at h
  unfold pairOf
  generalize q.splitOn ',' = L at h ⊢
  match L, h with
  | [a, b], h =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
      at h
    obtain ⟨⟨⟨ha, hb⟩, hda⟩, hdb⟩ := h
    simp only [List.map_cons, List.map_nil]
    rw [toNat?_digits hda ha, toNat?_digits hdb hb]
    rfl

theorem decodePairs_ofList {cs : List Char} (h : piecesOK cs = true) :
    decodePairs (String.ofList cs) = (cs.splitOn ';').filterMap pairOf := by
  unfold decodePairs
  rw [semi_eq, CFSG.KC.Str.splitOn_ofList, List.filterMap_map]
  apply List.filterMap_congr
  intro q hq
  exact piece_eq (List.all_eq_true.1 h q hq)

end CFSG.KC.G2Three

end
