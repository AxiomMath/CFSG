module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Numerics
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4

section Residuals

@[expose] def CentFiveA (G : Type) [Group G] : Prop :=
  ∀ k : G, orderOf k = 5 → InvertedByTwoA k →
    Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 5 * 273030912000000

theorem CentFiveA.of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (h : CentFiveA G') :
    CentFiveA G := by
  intro k hk hinv
  have h1 := h (e k) (by rw [MulEquiv.orderOf_eq]; exact hk) (hinv.map e)
  rwa [natCard_centralizer_mulEquiv] at h1

end Residuals

end CFSG.HardMathSupport.Dickson.I271
