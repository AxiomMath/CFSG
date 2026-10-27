module

public import Certificates.Data.CFSGNative.CTIB.Arith
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

public section

namespace CFSG.Monster.B.CTIB.Native

theorem parseWords_ofList (L : List Char) :
    parseWords (String.ofList L) =
      (List.splitOnPPrepend (· == ' ') L []).map (·.map letterOf) := by
  rw [parseWords, CFSG.KS.SporSch.LyTxt.splitOn_sp, List.map_map]
  congr 1
  funext w
  simp [String.toList_ofList]

end CFSG.Monster.B.CTIB.Native
