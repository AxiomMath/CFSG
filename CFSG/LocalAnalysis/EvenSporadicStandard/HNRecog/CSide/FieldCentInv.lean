module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FixOuter

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CSide
open scoped commutatorElement

theorem cSideFacts_centQ_inv :
    ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    AschbacherHyp C Q → ∀ t : C, (t : C ⧸ Q) ^ 2 = 1 → (t : C ⧸ Q) ≠ 1 →
      Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} = 2 ^ 5 := by
  intro C _ Q _ hC t ht2 ht1
  have hW : WeakHyp C Q := WeakHyp.of_aschbacherHyp hC
  haveI : Finite Q := hW.finite_Q
  haveI : Finite C := hW.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hW.isExtraspecialPGroup
  obtain ⟨S⟩ := hW.nonempty_setup
  by_cases htL : t ∈ commutator C
  · exact CSideSetup.card_comm_of_inner hW S htL ht2 ht1
  · have htq : t ^ 2 ∈ Q :=
      (QuotientGroup.eq_one_iff (t ^ 2)).mp (by rwa [QuotientGroup.mk_pow])
    rw [cSide_card_comm_eq hW.isExtraspecialPGroup t,
      cSide_card_fix_outer hC htL htq]
    norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
