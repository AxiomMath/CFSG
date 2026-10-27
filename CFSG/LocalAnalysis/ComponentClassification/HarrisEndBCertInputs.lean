module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelData
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelData
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG.ComponentClassification.J2Cover CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def c2AGens : List Table :=
  [arrTable 315 cent2AStrong[0]!, arrTable 315 cent2AStrong[1]!]

@[expose] def c2BGens : List Table :=
  [arrTable 315 cent2BStrong[0]!, arrTable 315 cent2BStrong[1]!]

@[expose] def crTGens : List Table :=
  [arrTable 315 crTStrong[0]!, arrTable 315 crTStrong[1]!, arrTable 315 crTStrong[2]!]

end CFSG.ComponentClassification.HarrisLit.EndB
