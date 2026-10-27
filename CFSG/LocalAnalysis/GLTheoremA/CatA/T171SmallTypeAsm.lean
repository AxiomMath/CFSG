module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAsmLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAsmAmbig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)


theorem t171SmallTypeFact_of_residuals
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hU42 : I1431C2.U42InnField) (hM : ModelRed) (hA : AlphaRed) (hA6 : A6InnField)
    (hE : ExcNoSmall) (hU : UniHighWit) (hLin : FamLin) (hU4 : FamU4) (hSp : FamSp)
    (hOmP : FamOmP) (hOmM : FamOmM) (hCard : BCardLe) (hW : Wit5False) :
    T171.T171SmallTypeFact := by
  intro Ω _ _ B x L hK hcfg hLn hMax hstd hsmall hT
  rcases hcfg.chev2 with hLie | hAmb
  · exact t171SmallTypeFact_of_lie hGA hU42 hM hA hA6 hE hU hLin hU4 hSp hOmP hOmM
      hCard hW hK hcfg hLn hMax hstd hsmall hT hLie
  · exact (false_of_ambiguousChev_two hcfg hAmb).elim

end CFSG.LocalAnalysis.GLTheoremA.T171S
