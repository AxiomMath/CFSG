module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Index
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Multi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.Sporadic.Schreier.PairJ2Cert
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Index
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Multi
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public meta import CFSG.Sporadic.SmallOddCore.J2Data
public meta import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2CheckInputs
public import Certificates.Certificate4127
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.Bridge.J2Excl

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem j2_perm_check :
    isInvA 315 j2A0A (invCand 315 j2A0A) = true ∧ isInvA 315 j2A1A (invCand 315 j2A1A) = true ∧
      ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 31], permOK 315 (j2CentTbl k) = true :=
  Certificates.certificate4127.1

theorem j2_row0_check :
    threeConjCheck 315 [j2A0P, j2A1P] (j2TP 9) j2Row0Words j2Row0Prog [j2A0A, j2A1A] = true :=
  Certificates.certificate4127.2.1

theorem j2_row1_check :
    threeConjCheck 315 [j2A0P, j2A1P] (j2TP 17) j2Row1Words j2Row1Prog [j2A0A, j2A1A] = true :=
  Certificates.certificate4127.2.2.1

theorem j2_row2_check :
    threeConjCheck 315 [j2A0P, j2A1P] (j2TP 31) j2Row2Words j2Row2Prog [j2A0A, j2A1A] = true :=
  Certificates.certificate4127.2.2.2.1

theorem j2_syl_check :
    sylVerify 315 256 j2SylGens j2Par j2Lab j2Tab j2Al 4 = true :=
  Certificates.certificate4127.2.2.2.2.1

theorem j2_idx_check :
    j2MulOK = true ∧ j2InvOK = true ∧ j2RepsOK = true ∧ j2TripleOK = true :=
  Certificates.certificate4127.2.2.2.2.2.1

theorem j2_pair_check : j2PairCertsOK = true :=
  Certificates.certificate4127.2.2.2.2.2.2.1

theorem j2_frob_check : j2FrobOK = true :=
  Certificates.certificate4127.2.2.2.2.2.2.2

end CFSG.QuasithinUnique.Bridge.J2Excl
