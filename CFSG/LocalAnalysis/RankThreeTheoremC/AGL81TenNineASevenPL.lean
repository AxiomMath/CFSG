module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineASevenPLExc
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineASevenPLNat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineNormalNX
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Smith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.HardMathSupport.Cooperstein

theorem asc81bASevenPLRankNX_holds :
    Asc81bASevenPLRankNX := by
  intro G _ _ M S L hX hA hL hnX ⟨e⟩
  have hSL := Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  rcases Coordinator.gf2NaturalSection_of hX hA hL hSL (Or.inl rfl)
      (nonempty_barM_sup_quot_center hA hL hSL e)
      (Coordinator.EightFive.gf2EightFive_of_b42L42Core Coordinator.EightFive.b42L42Core_holds)
      Coordinator.gf2NoFFTripleA7 with hN | ⟨-, hact, h16⟩
  · exact absurd (inClassXBlock_of_natural_seven hX hA hL hN) hnX
  · exact exists_elemAbelian_three_of_a7Exceptional hX hA hL hSL hnX e hact h16

end CFSG.LocalAnalysis.RankThreeTheoremC
