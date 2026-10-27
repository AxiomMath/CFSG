module

public import CFSG.HardMathSupport.Dickson.OddLieB2.Converter
public import CFSG.HardMathSupport.Dickson.OddLieB2.Classical
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest

public section

namespace CFSG.HardMathSupport.Dickson.OddLieB2

theorem lieClassicalOddCharTwoBp : CFSG.Yardstones.Md42047359a2a.LieClassicalOddCharTwoBp := by
  intro idx hfam hchar S _ _ hS hnc he
  haveI := hS
  exact simpleBp_two_of_fixedTwoComponentsQuasisimple hnc
    (fixedTwoComponentsQuasisimple_of_classical idx hfam hchar S hnc he)

theorem oddLieType_of_seitzBridge (hS : CFSG.RankThree.PartOne.CTP.SeitzBridge) {X : Type}
    [Group X] {d : TauCeti.LieTypeIndex} (h : CFSG.RankThree.PartOne.Census3.IsoLie X d)
    (hd : d.characteristic ≠ 2) : CFSG.Blueprint.OddLieType X := by
  obtain ⟨t, n, r, f, hadm, hmodel, hr, -, -⟩ := hS X d h
  exact ⟨t, n, r, f, hadm.1, hr ▸ hd, hadm, hmodel⟩


theorem catalogueBp_two_of_odd (idx : TauCeti.ValidLieTypeIndex)
    (hchar : idx.1.characteristic ≠ 2) :
    CFSG.Yardstones.Md42047359a2a.CatalogueBp 2 (TauCeti.CFSGIndex.lie idx) := by
  intro S _ _ hS hnc he
  haveI := hS
  exact simpleBp_two_of_fixedTwoComponentsQuasisimple hnc
    (CFSG.ComponentClassification.CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hnc
      (oddLieType_of_seitzBridge CFSG.RankThree.PartOne.CTP.seitzBridge ⟨idx.2, he⟩ hchar))

theorem lieExceptionalOddCharTwoBp :
    CFSG.Yardstones.Md42047359a2a.LieExceptionalOddCharTwoBp :=
  fun idx _ hchar => catalogueBp_two_of_odd idx hchar

end CFSG.HardMathSupport.Dickson.OddLieB2
