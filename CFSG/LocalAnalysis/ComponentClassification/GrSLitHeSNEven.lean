module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNHolt
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FieldSq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4WInv

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

structure EvenSylow (X : Type) [Group X] [Finite X] (a : X) (W K T : Subgroup X) : Prop where
  isSylow : IsSylowTwoIn T (normalizer (W : Set X))
  mem : a ∈ T
  isSylow_normalizer : IsSylowTwoIn (T ⊓ normalizer (K : Set X))
    (normalizer (W : Set X) ⊓ normalizer (K : Set X))
  isSylow_centralizer : IsSylowTwoIn (T ⊓ centralizer ({a} : Set X)) (centralizer ({a} : Set X))
  not_le : ¬ T ≤ normalizer (K : Set X)
  inf_coreKernel : T ⊓ coreKernel (normalizer (W : Set X)) K = ⊥

@[expose] def HeldSingleNormalEvenStep : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : X) (L W K T : Subgroup X),
    Setting X a L W K → EvenSylow X a W K T → False

end CFSG.ComponentClassification.GrSLit.HeSN
