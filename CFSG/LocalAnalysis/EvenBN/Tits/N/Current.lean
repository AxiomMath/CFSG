module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Final
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Step07
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Step09
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bM
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P2bN
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Step17
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Node20
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bFinal
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Step24Fin
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Step25
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Step26
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Node23a
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Node22
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Main
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14E
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11Final
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Step10
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Step05
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarKappa
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Node18
public import CFSG.LocalAnalysis.EvenBN.Tits.S56StepKappa
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S16End
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Step19

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N


theorem titsThm49StatementExclusion_of_open (sB : StepKappaBit) :
    CFSG.Yardstones.M41b0c98b3153.TitsThm49StatementExclusion :=
  titsThm49StatementExclusion_of_steps (Star.stepZ0Inv_of_kappa (stepKappa_of_bit sB)) (stepKappa_of_bit sB)
    step05_holds step07_holds step08_holds step09_holds step10_holds step11_holds step12_holds step13_holds
    step14_holds step15_holds step16_holds step17s_holds step17_holds
        (P5.step18_of_top CFSG.Goldschmidt.topStatement) step19_holds
    step19b_holds P5.step20_holds step21_holds (P5.step22_of_top CFSG.Goldschmidt.topStatement) P5.step23a_holds step23b_holds step23c_holds
    step24_holds step25_holds step26_holds

end CFSG.LocalAnalysis.EvenBN.Tits.N
