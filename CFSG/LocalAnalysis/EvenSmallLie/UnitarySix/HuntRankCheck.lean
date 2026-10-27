module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Certificate3003

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open CFSG.ComponentClassification.WittDesign

theorem search_check :
    rootCheck 256 tab8 list8 = true ∧ rootCheck 256 tab0 list0 = true ∧
    rootCheck 512 tabY listY = true ∧ list8.Pairwise (fun a b => keyT a < keyT b) ∧
    list0.Pairwise (fun a b => keyT a < keyT b) ∧
    listY.Pairwise (fun a b => keyT a < keyT b) :=
  Certificates.certificate3003.1

theorem count_miss :
    m22Count (fun f => (missOut (tf tab8) list8 f || missOut (tf tab0) list0 f ||
    missIn (tf tabY) listY f) = true) = 0 :=
  Certificates.certificate3003.2.1

theorem count_outer :
    m22Count (fun f => sqMulB (tf tab8) f = true) = 1716 :=
  Certificates.certificate3003.2.2.1

theorem count_inner :
    m22Count (fun f => (sqB f && !eqB id f) = true) = 1155 :=
  Certificates.certificate3003.2.2.2.1

theorem count_cent8 :
    m22Count (fun f => commB (tf tab8) f = true) = 1344 :=
  Certificates.certificate3003.2.2.2.2.1

theorem count_cent0 :
    m22Count (fun f => commB (tf tab0) f = true) = 320 :=
  Certificates.certificate3003.2.2.2.2.2.1

theorem count_centY :
    m22Count (fun f => commB (tf tabY) f = true) = 384 :=
  Certificates.certificate3003.2.2.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix.Hunt
