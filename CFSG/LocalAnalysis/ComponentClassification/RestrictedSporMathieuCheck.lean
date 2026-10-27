module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public import Certificates.Certificate2023

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Certificates

theorem m23_three_witness_check :
    threeWitnessOK 23 (listTables m23KGens) (listInvTables m23KGens)
      (toTable (evalCodes m23KGens [3, 3, 3])) (toTable (evalCodes m23KGens [3, 3])) 1000 =
      true :=
  Certificates.certificate2023.1

theorem m24_three_witness_check1 :
    threeWitnessOK 24 (listTables m24K1Gens) (listInvTables m24K1Gens)
      (toTable (evalCodes m24K1Gens [2, 2])) (toTable (evalCodes m24K1Gens [2, 1, 2, 1])) 1000 =
      true :=
  Certificates.certificate2023.2.1

theorem m24_three_witness_check2 :
    threeWitnessOK 24 (listTables m24K2Gens) (listInvTables m24K2Gens)
      (toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1]))
      (toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1])) 1000 = true :=
  Certificates.certificate2023.2.2.1

theorem m22_three_witness_check :
    threeWitnessOK 22 (listTables m22OKGens) (listInvTables m22OKGens)
      (toTable (evalCodes m22OKGens [1, 1])) (toTable (evalCodes m22OKGens [3, 1])) 1000 =
      true :=
  Certificates.certificate2023.2.2.2

end CFSG.ComponentClassification.RestrictedStd.Spor
