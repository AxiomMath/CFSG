module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSU38
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSLin1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DSDiagE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CIMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Certs


theorem t263Desc_lin_of_hi (h : T263Desc t263GLinHi) : T263Desc t263GLin :=
  t263Desc_of_cover t263GLin_cover t263Desc_linRk1 h

end Certs

structure T263DescClassicalResidual : Prop where
  linHi : T263Desc t263GLinHi
  uni : T263Desc t263GUni
  symp : T263Desc t263GSymp
  orth : T263Desc t263GOrth
  twOrth : T263Desc t263GTwOrth

structure T263DescClassicalSeeds : Prop where
  linHi : T263DescSeed t263GLinHi
  uni : T263DescSeed t263GUni
  symp : T263DescSeed t263GSymp
  orth : T263DescSeed t263GOrth
  twOrth : T263DescSeed t263GTwOrth

theorem T263DescClassicalSeeds.toResidual (R : T263DescClassicalSeeds) : T263DescClassicalResidual :=
  ⟨t263Desc_of_seed_proved R.linHi, t263Desc_of_seed_proved R.uni, t263Desc_of_seed_proved R.symp,
    t263Desc_of_seed_proved R.orth, t263Desc_of_seed_proved R.twOrth⟩

section Certs'


theorem t263OpenCellsRest_of_exc (R : T263DescClassicalResidual) (e6 : T263Desc t263GE6) (exc : T263Desc t263GExc)
    (td4 : T263Desc t263GTD4) (ree : T263Desc t263GRee) : T263OpenCellsRest :=
  ⟨t263Desc_lin_of_hi R.linHi, R.uni, R.symp, R.orth, R.twOrth, e6, exc, td4, ree, t263Desc_u38⟩

theorem t263OpenCellsRest_of_exc_seeds (R : T263DescClassicalSeeds) (e6 : T263Desc t263GE6) (exc : T263Desc t263GExc)
    (td4 : T263Desc t263GTD4) (ree : T263Desc t263GRee) : T263OpenCellsRest :=
  t263OpenCellsRest_of_exc R.toResidual e6 exc td4 ree

end Certs'

end CFSG.LocalAnalysis.GLTheoremA.T263

end
