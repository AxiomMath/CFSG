module

public import Certificates.Data.CFSGNative.CTIB.Arith
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import Std.Data.String.ToNat

public section

namespace CFSG.Monster.B.CTIB.Native

@[expose] def pieceVal (p : List Char) : Option Nat :=
  if p = [] then none else some (Nat.ofDigitChars 10 p 0)

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
      filterMap_congr' fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem parseNats_ofList (L : List Char)
    (h : ∀ p ∈ List.splitOnPPrepend (· == ' ') L [], ∀ c ∈ p, c.isDigit = true) :
    parseNats (String.ofList L) = (List.splitOnPPrepend (· == ' ') L []).filterMap pieceVal := by
  rw [parseNats, CFSG.KS.SporSch.LyTxt.splitOn_sp, List.filterMap_map]
  refine filterMap_congr' fun p hp => ?_
  rw [Function.comp_apply, pieceVal]
  by_cases he : p = []
  · rw [ite_eq_left he, he, Option.eq_none_iff_forall_ne_some]
    intro n hn
    exact (String.isNat_iff.1 (String.isNat_of_toNat?_eq_some hn)).1 rfl
  · rw [ite_eq_right he]
    exact CFSG.KS.SporSch.LyTxt.toNat_digits (h p hp) he

end CFSG.Monster.B.CTIB.Native

end
