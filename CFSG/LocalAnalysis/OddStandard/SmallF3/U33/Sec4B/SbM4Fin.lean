module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34El
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Glue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0z
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2z
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S3z
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S4z
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5z
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Glue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4QFin

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l411_syl_holds : L411SylStmt :=
  l411_syl_of_steps l34_s0 l34_s1 l34_s2 (L34Z.l34_s3_of_input L34E.l34SigmaFourInput_holds)
      L34Z.l34_s4 L34Z.l34_s5 l34_s6

theorem lemma4_11_of_ab (hI : Sec4Inputs) (hA : L411AbStmt) : Lemma4_11Stmt :=
  lemma4_11_of_steps hI l411_four_holds l411_q_holds l411_syl_holds hA

end CFSG.OddStandard.SmallF3.HarrisU33
