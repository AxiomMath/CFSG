module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public meta import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuCheckInputs
public import Certificates.Certificate4036
public meta import CFSG.Foundations
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuEnum

public section

namespace CFSG.QuasithinUnique.Bridge.RuExcl

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native

theorem ru_conjA_check :
    threeConjCheck 4060 [ruA0P, ruA1P] ruA0P ruAWords ruAProg [ruA0A, ruA1A] = true :=
  Certificates.certificate4036.1

theorem ru_conjZ_check :
    threeConjCheck 4060 [ruA0P, ruA1P] ruZtP ruZWords ruZProg [ruA0A, ruA1A] = true :=
  Certificates.certificate4036.2

end CFSG.QuasithinUnique.Bridge.RuExcl
