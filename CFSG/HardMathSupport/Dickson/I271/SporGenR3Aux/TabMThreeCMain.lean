module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeCGms
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence

section MGriess


theorem centThreeC_MGriess : CentThreeC MGriess := by
  intro k α hk3 hα2 hαc hαk hH
  have I := CFSG.YGroups.Y443.gmsInterfaces_MGriess
  have hG := gmsF1Type_MGriess_uncond
  have hex := oddExhaustive_MGriess I
  have hcls : ∀ β : MGriess, orderOf β = 2 →
      Nat.card ↥(Subgroup.centralizer ({β} : Set MGriess)) = 2 * monsterBabyOrder →
      IsConj tGriess β := by
    intro β hβ hβc
    rcases (CFSG.YGroups.Y443.monster_clauses_MGriess).2.1 β hβ with h | h
    · exact h
    · exfalso
      have h2 := (isTwoBCentralizer_MGriess β h).2.2.2.2.1
      rw [hβc] at h2
      norm_num [twoBCentralizerOrder, monsterBabyOrder] at h2
  exact TabMThreeC.card_centralizer_le_of_gms I hG hex hcls k α hk3 hα2 hαc hαk hH

section Iso


theorem centThreeC_M : CentThreeC (NativeSporadic.Carrier .M) := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  exact CentThreeC.of_equiv e.symm centThreeC_MGriess

end Iso

end MGriess

end CFSG.HardMathSupport.Dickson.I271
