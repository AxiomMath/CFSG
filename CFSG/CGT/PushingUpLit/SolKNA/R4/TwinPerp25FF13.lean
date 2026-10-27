module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF12
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FMix

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution

section Assembly


theorem c25_16invR_of_below {r n : ℕ} (hr : 5 ≤ r) (hNo : NoQ16E4) (h6 : C25_6R r n)
    (hB : Thm1RTwinBelowR (r - 1) n) : C25_16invR r n :=
  c25_16invR_of_parts h6 (mix14R_proof (by omega)) (zStarFFR_of_below hr hNo hB)

end Assembly

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
