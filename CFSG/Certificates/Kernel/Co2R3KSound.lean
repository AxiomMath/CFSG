module

public import Certificates.Data.Kernel.Co2R3K
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Co2Rank3.CheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
import CFSG.Certificates.Kernel.Co2R3KSnd.OrbReplay
import CFSG.Certificates.Kernel.Co2R3KSnd.Rec
import CFSG.Certificates.Kernel.Co2R3KSnd.Lists

public section

namespace CFSG.KC.Co2R3

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS.Raw CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Rank3.Native CFSG.Sporadic.FischerOddCore.Native

theorem orbReplay_sound {n m : Nat} {gens : Array (Array Nat)} {G : Nat → Nat}
    {L D P V O Q : Nat} (hn : n < 4096) (hgs : gens.size = m)
    (hG : ∀ k < m, gens[k]! = unpack n 12 (G k)) (h : orbReplayK n m G L D P V O Q = true) :
    orbitSearch n gens = (unpack n 12 L, unpack n 12 D, unpack n 12 P, unpack n 12 V) := by
  exact Snd.orbitSearch_eq_unpack hgs hG h

theorem rec_sound {m : Nat} {gens : Array (Array Nat)} {G : Nat → Nat} {L D P V : Nat}
    {roots : List (Nat × Nat)} (hgs : gens.size = m)
    (hG : ∀ k < m, gens[k]! = unpack 2300 12 (G k)) (h : recK m G L D P V roots = true) :
    recOK gens (unpack 2300 12 L, unpack 2300 12 D, unpack 2300 12 P, unpack 2300 12 V) roots =
      true := by
  exact Snd.recOK_of_recK hgs hG h

theorem listLabel_sound {n d a L : Nat} {R M S : Nat → Nat} {good : List Nat}
    (hrow : rowOK n d R M S a = true) (ha : a < n) (h : llK n M a L good = true) :
    listLabelOK n (rowsArr n d R)[a]! (unpack n 12 L) good = true := by
  exact Snd.listLabelOK_of_llK hrow ha h

theorem common_sound {d a b c : Nat} {R M S : Nat → Nat}
    (hra : rowOK 2300 d R M S a = true) (hrb : rowOK 2300 d R M S b = true) (ha : a < 2300)
    (hb : b < 2300) (h : ccK M a b c = true) :
    commonCount (rowsArr 2300 d R)[a]! (rowsArr 2300 d R)[b]! = c := by
  exact Snd.commonCount_of_ccK hra hrb ha hb h

theorem colourLabel_sound {n d k T L : Nat} {nbr : Array (List Nat)} {t : Array Nat}
    {R M S : Nat → Nat} {pre roots : List Nat} (hn0 : 0 < n) (hn : n < 4096) (hd : 0 < d)
    (hd' : d < 65536) (hnbr : nbr = rowsArr n d R) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (hsym : ∀ x < n, ∀ y ∈ nbr[x]!, x ∈ nbr[y]!) (ht : t = unpack n 12 T)
    (hpre : pre.length < 65536) (h : clabK n S T pre k L roots = true) :
    colourLabelOK n (colourT n nbr t pre k) (unpack n 12 L) roots = true := by
  exact Snd.colourLabelOK_of_clabK hn hnbr hrow hsym ht hpre h

end CFSG.KC.Co2R3

end
