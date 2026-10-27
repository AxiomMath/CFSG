module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.Spor.PointChainCard
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.CFSGNative.ONSchreier.Vectors

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native
open CFSG.ONSchreier.Native CFSG.Monster.B.Co2

theorem pointChainOK_of_card {n : Nat} {a0 a1 : Array Nat} {W : Array (List Int)}
    {base : Array Nat} {chunks : Nat}
    (hW : 2 ≤ W.size ∧ W[0]! = [] ∧ W[1]! = [] ∧ ∀ j < W.size, 2 ≤ j → plettersOK j W[j]! = true)
    (hperm : ∀ j < (strongArrs n a0 a1 W).size,
      pisInv n (strongArrs n a0 a1 W)[j]! (pinvCand n (strongArrs n a0 a1 W)[j]!) = true)
    (hb : ∀ i < base.size, base[i]! < n)
    (hcard : Nat.card (Subgroup.closure ({permOfArr n a0, permOfArr n a1} : Set (Equiv.Perm (Fin n)))) ≤
      (cOrbitSizes n (strongArrs n a0 a1 W) base).prod) :
    pointChainOK n 2 (strongArrs n a0 a1 W) base W chunks = true :=
  CFSG.KS.PCC.pointChainOK_of_card' hW hperm hb hcard

end CFSG.KS.ON

end
