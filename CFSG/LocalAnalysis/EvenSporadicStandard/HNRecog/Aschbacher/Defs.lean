module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

@[expose] def IsOuterInvolution (Q : Subgroup C) (t : C) : Prop :=
  t ∉ commutator C ∧ t ^ 2 = 1 ∧ ∀ T : Sylow 2 C, t ∈ T →
    ∃ x ∈ Q, (∀ s ∈ (T : Subgroup C) ⊓ commutator C, ⁅x, s⁆ ∈ centerOf Q) ∧
      ⁅t, x⁆ ∉ centerOf Q

theorem AschbacherHyp.exists_isOuterInvolution (hC : AschbacherHyp C Q) :
    ∃ t, IsOuterInvolution Q t :=
  hC.exists_involution

end CFSG.EvenSporadicStandard.HNRecog
