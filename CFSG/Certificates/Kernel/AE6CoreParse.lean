module

public import Certificates.Data.Kernel.AE6Core
import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.ExactGen.ParseSound

public section

namespace CFSG.KC.AE6Core

open CFSG.KC.ExactGen

theorem semi_eq : (";" : String) = String.singleton ';' := by decide

theorem comma_eq : ("," : String) = String.singleton ',' := by decide

theorem ofList_ne_empty (l : List Char) : decide (String.ofList l ≠ "") = !l.isEmpty := by
  cases l with
  | nil => simp
  | cons x xs =>
    have : String.ofList (x :: xs) ≠ "" := by
      intro h
      have := congrArg String.toList h
      simp at this
    simp [this]

theorem parseWords_ofList (cs : List Char) (h : toksOKw cs = true) :
    Certificates.S7Twin.parseWords (String.ofList cs) = wordsL cs := by
  have hws : (fun c : Char => !c.isWhitespace) = fun c => !isWs c := by
    funext c
    rw [isWs_eq]
  unfold Certificates.S7Twin.parseWords
  simp only
  rw [String.toList_ofList, hws, semi_eq, CFSG.KC.Str.splitOn_ofList, List.map_map]
  unfold toksOKw piecesL at h
  unfold wordsL piecesL
  rw [List.map_map]
  rw [List.all_map, List.all_eq_true] at h
  apply List.map_congr_left
  intro w hw
  have hw' := List.all_eq_true.1 (h w hw)
  simp only [Function.comp_apply] at hw' ⊢
  rw [comma_eq, CFSG.KC.Str.splitOn_ofList, List.filter_map]
  have e : ((fun s : String => decide (s ≠ "")) ∘ String.ofList) = fun l => !l.isEmpty := by
    funext l
    exact ofList_ne_empty l
  rw [e, List.map_map]
  exact List.map_congr_left fun t ht => toInt_ofList (hw' t ht)

end CFSG.KC.AE6Core

end
