module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeCheckInputs
public import Certificates.Certificate4134
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native

theorem he_conj0_check :
    threeConjCheck 8330 [heA0P, heA1P] heT0P heT0Words heT0Prog [heGen 0, heGen 1] = true :=
  Certificates.certificate4134.1

theorem he_conj1_check :
    threeConjCheck 8330 [heA0P, heA1P] heT1ArrP heT1Words heT1Prog [heGen 0, heGen 1] = true :=
  Certificates.certificate4134.2.1

theorem he_conjU_check :
    threeConjCheck 8330 [heA0P, heA1P] heUP heUWords heUProg [heGen 0, heGen 1] = true :=
  Certificates.certificate4134.2.2.1

theorem he_syl_check :
    sylVerify 8330 2048 heSylGens (parseNats heSylParStr) (parseNats heSylLabStr)
      (parseNats heSylTabStr) (sylBuild 8330 2048 heSylGens (parseNats heSylParStr)
        (parseNats heSylLabStr)) 6 = true :=
  Certificates.certificate4134.2.2.2

end CFSG.QuasithinUnique.Setup.X1
