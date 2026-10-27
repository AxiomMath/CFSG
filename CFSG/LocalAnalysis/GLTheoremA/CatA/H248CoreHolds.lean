module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CoreDefs
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CorePrimeG2
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CoreAssembly
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CoreRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CorePrimeLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248CoreSmall
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThreeSL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThreeSp
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThreeSU
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThreeBD
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThreeExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.AGLEmbedding

section Excl


theorem corePrimeExcl_holds : CorePrimeExcl := by
  intro p q hp hp2 hq hq2 hqp S _ _ d ⟨e⟩ ⟨Q, hQ, hQ1, hd⟩ A hA
  rcases hd with hd | hd | hd
  · exact card_lt_of_elemAbelian_mulAut_linThree hp hp2 hqp e hQ hQ1 hd hA
  · exact card_lt_of_elemAbelian_mulAut_spFour hp hp2 hq2 hqp e hQ hQ1 hd hA
  · exact card_lt_of_elemAbelian_mulAut_gTwo hp hp2 hq2 hqp e hQ hQ1 hd hA

end Excl

section Core


theorem coreFact_holds : CoreFact :=
  coreFact_of_parts CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (charPGen3At_or charPGen3At_sl <| charPGen3At_or charPGen3At_sp <|
      charPGen3At_or charPGen3At_su <| charPGen3At_or charPGen3At_bOdd <|
        charPGen3At_or charPGen3At_d <|
          charPGen3At_or charPGen3At_twistedD charPGen3At_exceptional)
    coreRankFour_holds corePrimeExcl_holds (coreSmallVac_of_i713 GL83.I713.i_7_13_1_holds)

end Core

end CFSG.LocalAnalysis.GLTheoremA.H248
