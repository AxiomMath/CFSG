module

public import Certificates.Data.Kernel.Odd87CCK
import CFSG.Certificates.Kernel.Griess13.SLPTextSound

public section

namespace CFSG.KC.Odd87CCK

open Certificates.Odd87F3

theorem splitSp_eq : ∀ (cs acc : List Char),
    splitSp cs acc = List.splitOnPPrepend (· == ' ') cs acc
  | [], acc => by rw [splitSp, List.splitOnPPrepend_nil]
  | c :: cs, acc => by
    rw [splitSp, List.splitOnPPrepend_cons_eq_ite, List.splitOnP_eq_splitOnPPrepend,
      splitSp_eq cs [], splitSp_eq cs (c :: acc)]

theorem splitOn_sp (cs : List Char) :
    (String.ofList cs).splitOn " " = (splitSp cs []).map String.ofList := by
  rw [CFSG.KC.G13.splitOn_space, splitSp_eq, List.splitOn_eq_splitOnP,
    List.splitOnP_eq_splitOnPPrepend]

theorem pieces_eq (cs : List Char) :
    ((String.ofList cs).splitOn " ").filter (fun t => t.length > 0) =
      ((splitSp cs []).filter fun t => t.length > 0).map String.ofList := by
  rw [splitOn_sp, List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  simp [Function.comp, String.length_ofList]

theorem decodeWords_eq (s : String) : decodeWords s = wordsL s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [decodeWords, wordsL, pieces_eq, List.map_map]
  congr 1
  funext t
  simp [String.toList_ofList]

theorem decodeCov_eq (s : String) : decodeCov s = covL s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [decodeCov, covL, pieces_eq, List.map_map]
  congr 1
  funext t
  simp [String.toList_ofList]

end CFSG.KC.Odd87CCK
