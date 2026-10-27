module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallHeGen
public import CFSG.Sporadic.HeldB.AllFixed
public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.Sporadic.HeldB.InnerRestrict
public meta import CFSG.Sporadic.HeldB.OuterCentRestrict
public meta import CFSG.GH74.KGroups.PermCheck
public import Certificates.Certificate2110
public import Certificates.Certificate2111
public import Certificates.Certificate2112
public import Certificates.Certificate2114
public import Certificates.Certificate2116
public import Certificates.Certificate2223
public import Certificates.Certificate2224
public import Certificates.Certificate2225
public import Certificates.Certificate2115
public import Certificates.Certificate2117
public import Certificates.Certificate2118
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.ComponentClassification.CatFactsSmall.He

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct

@[expose] def y00 : Equiv.Perm (Fin 240) :=
  heInnerSigmaP0 3 * heInnerSigmaP0 8 * heInnerSigmaP0 4 * heInnerSigmaP0 1

@[expose] def y01 : Equiv.Perm (Fin 240) :=
  heInnerSigmaP0 6 * heInnerSigmaP0 4 * heInnerSigmaP0 1 * heInnerSigmaP0 7 * heInnerSigmaP0 4 *
    heInnerSigmaP0 5

@[expose] def QY0 : RawSchreierDatum 240 :=
  certificate (by decide) [tab y00, tab y01]
    [[2, 2, 1, 1], [1, 2, 2, 1, 1, 2, 1, 2], [2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2]]
    #v[0, 1, 2] (by decide)

@[expose] def yu0 : Equiv.Perm (Fin 98) :=
  heSigma2P * heSigma1P * heSigma2P * heSigma1P * heSigma1P * heSigma2P * heSigma1P

@[expose] def yu1 : Equiv.Perm (Fin 98) :=
  heSigma2P * heSigma1P * heSigma1P * heSigma2P * heSigma1P * heSigma2P * heSigma1P

@[expose] def QYu : RawSchreierDatum 98 :=
  certificate (by decide) [tab yu0, tab yu1] [[1, 2, 1, 2], [1, 2, 2, 2]] #v[0, 8] (by decide)

end CFSG.ComponentClassification.CatFactsSmall.He
