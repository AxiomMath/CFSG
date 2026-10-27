module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.CaseInner
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.BaseLe

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem cSideFacts_centQ_inv_base :
    ∀ (C : Type) [Group C] (Q : Subgroup C) [Q.Normal],
    IsExtraspecialPlusByA5WrTwoWith C Q → CIrreducible C Q → ∀ t : C,
      (t : C ⧸ Q) ^ 2 = 1 → (t : C ⧸ Q) ≠ 1 → (t : C ⧸ Q) ∈ commutator (C ⧸ Q) →
        Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} = 2 ^ 5 := by
  intro C _ Q _ hE hI t ht2 ht1 htL
  have hC : CSide.WeakHyp C Q := CSide.WeakHyp.of_cIrreducible hE hI
  haveI : Finite C := hC.finite
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hC.isExtraspecialPGroup
  obtain ⟨S⟩ := hC.nonempty_setup
  exact CSide.CSideSetup.card_comm_of_inner hC S
    (CSide.mem_commutator_of_mk_mem hC.le_commutator htL) ht2 ht1

end CFSG.EvenSporadicStandard.HNRecog.Section3
