module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerExcl
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBRealSound
public import Certificates.Certificate7264
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.SectionRank.QTK.CentreFact

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.QTK.CoverB

theorem j3Real_check :
    RealData.checkElem (ops2 80) j3Real = true :=
  Certificates.certificate7264

theorem realLocalElement_J3 :
    RealLocalElement (CFSG.Blueprint.NativeSporadic.Carrier .J3) 3 :=
  RealData.realLocalElement_of_checkElem (spec2 80) j3Real j3Real_check

theorem layerPairJ3_holds : LayerPairJ3 :=
  layerPairJ3_of_realLocalElement realLocalElement_J3

end CFSG.SectionRank.QTK.CentreFact
