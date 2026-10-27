module

import CFSG.ClassicalInvolution.Q3.TL3S8BWeak
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

section BP

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace Sec19Data3

variable (hd : Sec19Data3 K z S W)
include hd

theorem inf_mem_USet : K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
  CFSG.ClassicalInvolution.Q3.TightSylowData.inf_mem_USet hd.toTL3

end Sec19Data3

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem mem_W_z : z ∈ W :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.mem_W_z hd.toTL3

theorem le_normalizer_W : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.le_normalizer_W hd.toTL3

end Sec19DataT3

namespace Sec19DataT3

variable (hd : Sec19DataT3 K z S W L t V)
include hd

theorem mem_centralizerModOdd_K {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxR : x ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) :
    x ∈ centralizerModOdd ⊤ K :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.mem_centralizerModOdd_K hd.toTL3 hxS hxR

theorem mem_sec19BPrime_iff {x : G} :
    x ∈ S19B.sec19BPrime K S W L ↔
      x ∈ (S : Subgroup G) ∧ x ∈ centralizerModOdd ⊤ K ∧ x ∈ centralizerModOdd ⊤ L :=
  CFSG.ClassicalInvolution.Q3.TightSylowDataT.mem_sec19BPrime_iff hd.toTL3

end Sec19DataT3

end BP

end CFSG.ClassicalInvolution.Q3.Q3T6
