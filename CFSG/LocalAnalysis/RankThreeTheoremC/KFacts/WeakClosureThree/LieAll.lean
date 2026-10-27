module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieDef
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossPSU
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossSpO
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossExc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

section All


theorem dichLieCross_all : ∀ t, DichLieCrossAt t := by
  have hLie := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  intro t
  cases t
  · exact dichLieCross_PSL hLie
  · exact dichLieCross_PSU hLie
  · exact dichLieCross_PSp
  · exact dichLieCross_POmegaOdd
  · exact dichLieCross_POmegaPlus
  · exact dichLieCross_POmegaMinus
  · exact dichLieCross_G2 hLie
  · exact dichLieCross_F4
  · exact dichLieCross_E6
  · exact dichLieCross_E7
  · exact dichLieCross_E8
  · exact dichLieCross_twistedE6
  · exact dichLieCross_trialityD4 hLie
  · exact dichLieCross_twistedB2
  · exact dichLieCross_twistedG2
  · exact dichLieCross_twistedF4
  · exact dichLieCross_Tits

theorem dichThreeLie_holds : DichThreeLie :=
  dichThreeLie_of_tags dichLieDef_all dichLieCross_all

theorem heisDichLieCross_all : ∀ t, HeisDichLieCrossAt t := by
  have hLie := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  intro t
  cases t
  · exact (dichLieCross_PSL hLie).heis
  · exact (dichLieCross_PSU hLie).heis
  · exact dichLieCross_PSp.heis
  · exact dichLieCross_POmegaOdd.heis
  · exact dichLieCross_POmegaPlus.heis
  · exact dichLieCross_POmegaMinus.heis
  · exact heisDichLieCross_G2
  · exact dichLieCross_F4.heis
  · exact dichLieCross_E6.heis
  · exact dichLieCross_E7.heis
  · exact dichLieCross_E8.heis
  · exact dichLieCross_twistedE6.heis
  · exact heisDichLieCross_trialityD4
  · exact dichLieCross_twistedB2.heis
  · exact dichLieCross_twistedG2.heis
  · exact heisDichLieCross_twistedF4
  · exact dichLieCross_Tits.heis

theorem heisDichThreeLie_holds : HeisDichThreeLie :=
  heisDichThreeLie_of_tags dichLieDef_all heisDichLieCross_all

end All

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
