module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3M

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.Monster.Existence CFSG.Monster.Existence.Compat
  CFSG.Open CFSG.EvenSporadicStandard.Induction

section Pinned


theorem monsterInvolutions_pinned : MonsterInvolutions (Carrier .M) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_mGriess_of_isSporadic (Y := Carrier .M) ⟨MulEquiv.refl _⟩
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  exact MonsterInvolutions.of_mulEquiv φ
    (monsterInvolutions_of_existence hE twoARemaining.toFacts.b_card)

theorem hyp31RowFacts_m_pinned (inp : MHyp31Inputs) :
    Hyp31RowFacts MIsK [.M] [] [.B] :=
  hyp31RowFacts_m twoARemaining.toFacts mFacts monsterInvolutions_pinned inp

section PinnedB

theorem hyp31RowFacts_b_pinned (lit : Sol78Lit) (inp : BHyp31Inputs) :
    Hyp31RowFacts BIsK [.B] [.M] [] :=
  hyp31RowFacts_b lit.hyp12Lie twoARemaining.toFacts mFacts monsterInvolutions_pinned
    mPinnedFacts.rank babyTableIII e6TwoUnique lieModelOrders inp

end PinnedB

end Pinned

end CFSG.EvenSporadicStandard.Induction.Hyp
