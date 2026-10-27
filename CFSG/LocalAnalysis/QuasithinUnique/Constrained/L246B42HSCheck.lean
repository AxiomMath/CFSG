module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.Schreier.PairHSCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSCheckInputs
public import Certificates.Certificate4126
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.Bridge.HSExcl

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem hs_conj0_check :
    threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 5) hsT0Words hsT0Prog [hsA0A, hsA1A] = true :=
  Certificates.certificate4126.1

theorem hs_conj1_check :
    threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 12) hsT1Words hsT1Prog [hsA0A, hsA1A] = true :=
  Certificates.certificate4126.2.1

theorem hs_conj2_check :
    threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 21) hsT2Words hsT2Prog [hsA0A, hsA1A] = true :=
  Certificates.certificate4126.2.2.1

theorem hs_conj3_check :
    threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 34) hsT3Words hsT3Prog [hsA0A, hsA1A] = true :=
  Certificates.certificate4126.2.2.2.1

theorem hs_perm_check :
    isInvA 3850 hsA0A (invCand 3850 hsA0A) = true ∧
      isInvA 3850 hsA1A (invCand 3850 hsA1A) = true ∧
      ∀ k ∈ [1, 2, 3, 4, 5, 12, 21, 34], permOK 3850 (hsCentTbl k) = true :=
  Certificates.certificate4126.2.2.2.2.1

theorem hs_syl_check :
    sylVerify 3850 1024 hsSylGens (parseNats hsSylParStr) (parseNats hsSylLabStr)
      (parseNats hsSylTabStr) (sylBuild 3850 1024 hsSylGens (parseNats hsSylParStr)
        (parseNats hsSylLabStr)) 6 = true :=
  Certificates.certificate4126.2.2.2.2.2

end CFSG.QuasithinUnique.Bridge.HSExcl
