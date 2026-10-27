module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem rawChainK_of_card {n w kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} (chunks : Nat)
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (_hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hcard : Nat.card (Subgroup.closure (Set.range fun j : Fin kO => permOfArr n S[j.val]!)) ≤
      (rawOrbitSizes n S base).prod) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true := by
  obtain ⟨hk, hH⟩ := Orb.rawHeadOK_of hb hh
  exact Orb.rawChainOK_of_head_card chunks hk hH hcard

end CFSG.KS.Raw

end
