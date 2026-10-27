module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Native

theorem hG5_MGriess (hE : MonsterExistenceStatement MGriess) :
    ∀ A : Subgroup MGriess, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card ↥A → ∃ u ∈ A, orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set MGriess)) = twoBCentralizerOrder := by
  intro A hAc hAe h8
  obtain ⟨⟨hfin, -, -, -⟩, a, z, ha, hz, -, hcls, hA, hB, hgraph⟩ := id hE
  obtain ⟨-, c, -, -, hc1, -, -, -, -, hshape, -⟩ := hgraph
  haveI : Finite MGriess := hfin
  obtain ⟨u, hu, hzu⟩ := exists_twoB_of_elemAbelian babyTableIII babyTableIV
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat.nineteen_dvd_of_lieModel ha hA
    hc1 hshape hcls A hAc hAe h8
  refine ⟨u, hu, ?_, (hB u hzu).2.2.2.2.1⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hzu
  have h := MulEquiv.orderOf_eq (MulAut.conj g) z
  rw [MulAut.conj_apply, hg, hz] at h
  exact h

end Native

end CFSG.HardMathSupport.Dickson.I271.TabMFive
