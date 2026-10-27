module

import CFSG.ClassicalInvolution.Q3.TL3S8BF2
import CFSG.ClassicalInvolution.Q3.Q3T6OpenTL3
public import CFSG.ClassicalInvolution.AschTight.S19BStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6MainData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section F2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem conj_mem_sec19BPrime {x d : G} (hx : x ∈ S19B.sec19BPrime K S W L)
    (hdz : d * z = z * d) (hdS : d * x * d⁻¹ ∈ (S : Subgroup G)) :
    d * x * d⁻¹ ∈ S19B.sec19BPrime K S W L :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.conj_mem_sec19BPrime hd.toTL3 hx hdz hdS

end Sec19DataT3

end F2

end CFSG.ClassicalInvolution.Q3.Q3T6
