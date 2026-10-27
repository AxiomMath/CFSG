module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF13
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF17
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinTower

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

section Main


theorem c25_16invR_of_lowerTwin {r n : ℕ} (hr : 4 ≤ r) (hNo : NoQ16E4) (h6 : C25_6R r n)
    (hL : LowerTwinR r n) (h4 : TwinCentral4 n) : C25_16invR r n := by
  rcases Nat.lt_or_ge 4 r with h5 | h5
  · exact c25_16invR_of_below (by omega) hNo h6 (hL.1 (by omega))
  · obtain rfl : r = 4 := by omega
    exact c25_16invR_of_parts h6 (mix14R_proof le_rfl) (zStarFFR_four h4 (hL.2 rfl))

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
