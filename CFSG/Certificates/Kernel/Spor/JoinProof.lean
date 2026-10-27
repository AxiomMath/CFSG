module

public import CFSG.Certificates.Kernel.Spor.JoinSound

public section

namespace CFSG.KS.Join

open CFSG.KS.Raw

theorem hexT_join_proved {cs : List Char} {d n₀ w c N : Nat} {Fc F : Nat → Nat}
    (hx : CFSG.KC.Misc.HexFlat.hexFlat cs d n₀ w (c * N) Fc = true)
    (hj : joinK c (w * n₀) Fc F N = true) (hw : w ≤ 32) (_hw0 : 0 < w) (_hn : 0 < n₀) :
    ∀ j < N, CFSG.Sporadic.SmallOddCore.Native.natArr
      (CFSG.Sporadic.SmallOddCore.Native.hexT d (c * n₀) (c * n₀ * j) (String.ofList cs)) =
        unpack (c * n₀) w (F j) :=
  hexT_join_sound hx hj hw

end CFSG.KS.Join

end
