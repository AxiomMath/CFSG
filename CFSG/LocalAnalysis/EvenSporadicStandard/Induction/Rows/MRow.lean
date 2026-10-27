module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MOddCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMRow
import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Monster.Generated
  CFSG.RankThree.PartOne.SPOR CFSG.YGroups.Y443

@[expose] def MFixesElem : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover .M L →
    MPair H L K u → InvolutionFixesElem ↥K 8

theorem isMPairShape_mPair : IsMPairShape MPair := fun _ _ _ _ _ h => h

theorem sol78SettingLocalQ_m (hmult : OddMultTrivial .M) :
    Sol78SettingLocalQ .M MPair MPair :=
  sol78SettingLocalQ_of_monsterFacts isMPairShape_mPair hmult
    fun _ _ h => monsterFacts_of_isSporadic h

theorem sol78Local39Q_m (hmult : OddMultTrivial .M) : Sol78Local39Q .M MPair :=
  sol78Local39Q_of_monsterFacts isMPairShape_mPair hmult fun _ _ h => monsterFacts_of_isSporadic h

theorem nonempty_mulEquiv_mGriess_of_isSporadic {Y : Type} [Group Y]
    (h : NativeSporadic.IsSporadic Y .M) : Nonempty (Y ≃* MGriess) := by
  obtain ⟨e⟩ := h
  exact CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived.symm.nonempty_mulEquiv
    ⟨e⟩

theorem monsterOddCore_of_isSporadic {Y : Type} [Group Y] (h : NativeSporadic.IsSporadic Y .M) :
    InvolutionOddCoreTrivial Y := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_mGriess_of_isSporadic h
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  exact InvolutionOddCoreTrivial.of_mulEquiv φ
    (monsterOddCore_of_existence hE twoARemaining.toFacts)

theorem lemma36DataQ_m (hmult : OddMultTrivial .M) (hfix : MFixesElem) :
    Lemma36DataQ .M MPair 1 8 :=
  lemma36DataQ_of_monsterFacts isMPairShape_mPair hmult
    (fun _ _ h => monsterFacts_of_isSporadic h) hfix

theorem fusionRowData_m : FusionRowData .M (fun _ _ _ => False) := by
  have key : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M →
      AutCenterCond Y ∧ UMovesCond Y ∧ AutOddCoreTrivial Y := by
    intro Y _ h
    have hMf := monsterFacts_of_isSporadic h
    have := hMf.simple
    obtain ⟨e⟩ := h
    obtain ⟨hinn, hcen, hcomm⟩ := m_data_of_simple e
    have hZ : center Y = ⊥ := center_eq_bot_of_simple_nonabelian hMf.nonabelian
    exact ⟨autCenterCond_of_inner hinn hZ hcen, umovesCond_of_inner hinn hZ hcomm,
      autOddCoreTrivial_of_allInner hinn hZ (monsterOddCore_of_isSporadic ⟨e⟩)⟩
  exact ⟨fun Y _ h => (key Y h).1.toExc, fun Y _ h => (key Y h).2.1,
    fun Y _ h => (key Y h).2.2⟩

theorem mPair_inL : PairClass.InL MPair := fun _ _ _ _ _ h => h.1

theorem excExcluded_m : ExcExcluded .M (fun _ _ _ => False) MPair := by
  intro H _ _ N L K t u hcov hset hQ u₁ hN _ _ _ h
  exact h

theorem solomonCoreP_m : SolomonCoreP .M MPair :=
  solomonCoreP_of_fusion .M (fun _ _ _ => False) MPair mPair_inL fusionRowData_m excExcluded_m

theorem sol78Closing_m (hmult : OddMultTrivial .M) : Sol78Closing [.M] (fun _ => MPair) :=
  sol78Closing_of_partsP (S := [.M]) (Q := fun _ => MPair) (P := fun _ => MPair)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78SettingLocalQ_m hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact sol78Local39Q_m hmult)
    (fun s hs => by rcases List.mem_singleton.1 hs with rfl; exact solomonCoreP_m)

end CFSG.EvenSporadicStandard.Induction
