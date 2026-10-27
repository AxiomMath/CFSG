module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenHSActualSupplier

public section

namespace CFSG.OddStandard.AltStdSec.TenHSActualV4Support

open Subgroup Equiv Equiv.Perm
open CFSG.OddStandard.AltStdSec
open CFSG.OddStandard.AltStdSec.SwapPattern
open CFSG.OddStandard.AltStdCycTwo.Two
open CFSG.OddStandard.AltStdSec.TenHSActualSupplier
open CFSG.OddStandard.AltStdSec.TenHSOddKernelLift

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}
  {ε : ℕ} {x : G}

@[expose]
noncomputable def secMapO (x : G) :
    CFSG.OddStandard.AltStdSec.TenHSActualSupplier.H x →* TwoSecO x :=
  (QuotientGroup.mk' (CFSG.oddCore (TwoSec x))).comp
    (QuotientGroup.mk' (Subgroup.zpowers (selfC (G := G) x)))

end CFSG.OddStandard.AltStdSec.TenHSActualV4Support

end
