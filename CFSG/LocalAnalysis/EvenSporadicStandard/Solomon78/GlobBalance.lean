module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG CFSG.GH74.GLS CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.I32

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isTwoComponentIn_of_quasisimple_normal {X B : Subgroup G} (hBX : B ≤ X)
    (hq : IsQuasisimple ↥B) (hn : (B.subgroupOf X).Normal) : IsTwoComponentIn B X := by
  have hq' : IsQuasisimple ↥(B.subgroupOf X) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBX).symm hq
  have hcomp : IsComponent (B.subgroupOf X) := ⟨hq', hn.isSubnormal⟩
  have hP : IsPComponent 2 (B.subgroupOf X) :=
    LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hcomp
  exact (isTwoComponentIn_iff hBX).2
    ((ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).1 hP)

end CFSG.EvenSporadicStandard.Solomon78
