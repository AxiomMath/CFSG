module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Stage2

variable {S : Set (Subgroup G)} {N K1 K2 : Subgroup G}

abbrev O (N : Subgroup G) : Subgroup ↥N := pPrimeCore 2 ↥N

noncomputable abbrev pi (N : Subgroup G) : ↥N →* (↥N ⧸ O N) :=
  QuotientGroup.mk' (O N)

noncomputable abbrev QN (S : Set (Subgroup G)) (T : Type*) [Group T]
    (N : Subgroup G) : Subgroup ↥N :=
  (wholeKernel S T N).subgroupOf N

noncomputable abbrev X (S : Set (Subgroup G)) (T : Type*) [Group T]
    (N : Subgroup G) : Subgroup (↥N ⧸ O N) :=
  (QN S T N).map (pi N)

noncomputable abbrev F (S : Set (Subgroup G)) (T : Type*) [Group T]
    (N : Subgroup G) : Subgroup (↥N ⧸ O N) :=
  (generalizedFitting ↥(X S T N)).map (X S T N).subtype

end Stage2

end CFSG.ComponentClassification.FooteMarked

end
