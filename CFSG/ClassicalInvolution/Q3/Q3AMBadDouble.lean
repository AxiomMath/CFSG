module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Defs


@[expose] def PspNbhdDouble {G : Type} [Group G] (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    Prop :=
  ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι
      (↥(centralizingLayer (nbrCoreFam Ω M a) {a}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer (nbrCoreFam Ω M a) {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a})
        (centralizingLayer (nbrCoreFam Ω M a) {a})))),
    ∃ ha : a ∈ centralizingLayer (nbrCoreFam Ω M a) {a},
      ShapeDouble D (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(centralizingLayer (nbrCoreFam Ω M a) {a})) ⟨a, ha⟩)

@[expose] def C28_DoubleB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    PspSetting Ω K J S R T W z t K' → PspNbhdDouble Ω K z → False

end Defs

end CFSG.ClassicalInvolution.Q3.Q3AM
