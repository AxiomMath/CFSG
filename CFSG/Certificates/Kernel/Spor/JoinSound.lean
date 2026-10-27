module

public import CFSG.Certificates.Kernel.Spor.JoinCore

public section

namespace CFSG.KS.Join

open CFSG.KS.Raw

theorem hexTable_join_sound {cs : List Char} {d n₀ w c N : Nat} {Fc F : Nat → Nat}
    (hx : CFSG.KC.Misc.HexFlat.hexFlat cs d n₀ w (c * N) Fc = true)
    (hj : joinK c (w * n₀) Fc F N = true) :
    ∀ j < N, CFSG.Monster.B.Co2.Native.hexTable d (c * n₀) (c * n₀ * j) (String.ofList cs) =
      unpack (c * n₀) w (F j) :=
  hexTable_join_core hx hj

theorem hexT_join_sound {cs : List Char} {d n₀ w c N : Nat} {Fc F : Nat → Nat}
    (hx : CFSG.KC.Misc.HexFlat.hexFlat cs d n₀ w (c * N) Fc = true)
    (hj : joinK c (w * n₀) Fc F N = true) (hw : w ≤ 32) :
    ∀ j < N, CFSG.Sporadic.SmallOddCore.Native.natArr
      (CFSG.Sporadic.SmallOddCore.Native.hexT d (c * n₀) (c * n₀ * j) (String.ofList cs)) =
        unpack (c * n₀) w (F j) :=
  hexT_join_core hx hj hw

end CFSG.KS.Join

end
