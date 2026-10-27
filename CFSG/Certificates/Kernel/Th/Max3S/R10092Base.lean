
module

public import CFSG.Certificates.Kernel.Th.Max3S.Leaves
public import CFSG.Certificates.Kernel.Th.Spec.Big

@[expose] public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec

theorem nfIdx_lt {s : ℕ} {e : Fin 8 → ℕ} (hs : s < 2) (he : ∀ j, e j < 2) : nfIdx s e < 512 := by
  have := he 0; have := he 1; have := he 2; have := he 3; have := he 4; have := he 5; have := he 6
  have := he 7
  unfold nfIdx
  omega

end CFSG.KC.Th.Max3S

end
