module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenHSOddKernelLiftTwoSec
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapData
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSFacts

public section

namespace CFSG.OddStandard.AltStdSec.TenHSActualSupplier

open Subgroup Equiv Equiv.Perm
open CFSG.OddStandard.AltStdSec
open CFSG.OddStandard.AltStdSec.SwapPattern
open CFSG.OddStandard.AltStdCycTwo.Two
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.OddStandard.AltStdSec.TenHSOddKernelLift
open CFSG.EvenSporadicStandard.HSStd
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}
  {ε : ℕ} {x : G}

noncomputable abbrev H (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

end CFSG.OddStandard.AltStdSec.TenHSActualSupplier

end
