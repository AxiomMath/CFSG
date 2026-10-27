module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.MRowFinal
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.RankThree.PartOne.SPOR.OuterB
import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.Monster.Existence.Compat
  CFSG.Monster.Generated CFSG.RankThree.PartOne.SPOR CFSG.YGroups.Y443

@[expose] def MPair (G : Type) [Group G] (L K : Subgroup G) (u : G) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ 2 * monsterBabyOrder ≤ Nat.card K

theorem monsterFacts_of_isSporadic {Y : Type} [Group Y] (h : NativeSporadic.IsSporadic Y .M) :
    MonsterFacts Y := by
  obtain ⟨e⟩ := h
  have hMs : IsSimpleGroup (NativeSporadic.Carrier .M) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.isSimpleGroup_y443Derived
  have hs : IsSimpleGroup Y := @MulEquiv.isSimpleGroup _ _ _ _ hMs e
  have hY : AllInner Y := (m_data_of_simple e).1
  obtain ⟨ε⟩ : Nonempty (Y ≃* CFSG.Monster.Generated.Gmat) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.nonempty_mulEquiv_gmat_of_isSimpleGroup e
  have hGA : CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.gmat_eq_griess
  let φ : Y ≃* MGriess := ε.trans (griessEquivGmat hGA).symm
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  exact MonsterFacts.of_mulEquiv φ (monsterFacts_of_existence hE (twoARemaining.toFacts)
    allInner_B (AllInner.of_mulEquiv φ hY)) hY

end CFSG.EvenSporadicStandard.Solomon78
