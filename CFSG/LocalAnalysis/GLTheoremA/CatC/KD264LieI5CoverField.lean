module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5CoverLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5FieldReduce
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5SUClosed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.LieType.SemisimpleCentralizers.HeldLang

theorem kd264I5Field_of_certificates
    (hC : KD264I5CoverLiftExc) (hU : KD264I5UniversalExc) : KD264I5Field :=
  kd264I5Field_of_pieces (kd264I5CoverLift_of_inputs i5SUClosed_of_certificates hC)
    (kd264I5Universal_of_certificates hU)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
