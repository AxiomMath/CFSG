module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoSecTheta

public section

namespace CFSG.OddStandard.AltStdSec.TenHSOddKernelLift

open Subgroup
open CFSG.OddStandard.AltStdSec
open CFSG.OddStandard.AltStdCycTwo.Two

@[expose]
noncomputable def twoSecK0 {G : Type} [Group G] (x : G)
    (W : Subgroup (TwoSecO x)) : Subgroup ↥(Subgroup.centralizer ({x} : Set G)) :=
  let p : ↥(Subgroup.centralizer ({x} : Set G)) →* TwoSec x :=
    QuotientGroup.mk' (Subgroup.zpowers (selfC (G := G) x))
  let q : TwoSec x →* TwoSecO x :=
    QuotientGroup.mk' (CFSG.oddCore (TwoSec x))
  let E : Subgroup (TwoSec x) := W.comap q
  let K : Subgroup E := commutator E
  let J : Subgroup (TwoSec x) := K.map E.subtype
  ⁅J.comap p, J.comap p⁆

end CFSG.OddStandard.AltStdSec.TenHSOddKernelLift

end
