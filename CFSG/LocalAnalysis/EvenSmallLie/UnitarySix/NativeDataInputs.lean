module

public import CFSG.Fischer.T46Simple
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.SetOrbitTools
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public meta import Certificates.Data.CFSGNative.Fi22.Local
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Fi22.Native
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native

@[expose] def letterT (k : ℕ) : Table := t46Gen ((k : ℤ) + 1)

@[expose] def involOK (T : Table) : Bool :=
  allIn 0 693 (fun i => decide (ap T i < 693)) && invoOK 693 T

end CFSG.EvenSmallLie.UnitarySix
