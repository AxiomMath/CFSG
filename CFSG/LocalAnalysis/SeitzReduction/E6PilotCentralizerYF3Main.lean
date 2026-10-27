module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYPerfect
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K]

theorem perfectCore_centralizer_yD_eq_of_le [Finite K] [CharP K 2]
    (hUB : centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K)) ≤
      yRadical K ⊔ yLevi K ⊔ yTorus K) :
    perfectCore (centralizer ({e6Rep K 1} : Set (adjointGroup .E6 K))) =
      yRadical K ⊔ yLevi K :=
  perfectCore_centralizer_yD_eq commutator_yRadical_sup_yLevi hUB

end CFSG.SeitzReduction.E6Pilot
