
module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.J2.Certificate
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import Certificates.Data.CFSGNative.J2.Certificate
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

@[expose] public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native

theorem inv_check :
    invoList 315 outerArr = true ∧ movesList 315 outerArr = true ∧ invoList 315 twoAArr = true ∧
      movesList 315 twoAArr = true := by
  decide +kernel

theorem stab_check :
    autStrong[2]![0]! = 0 ∧ autStrong[3]![0]! = 0 ∧ autStrong[4]![0]! = 0 ∧
      (List.range 315).all (fun j => j == 0 || autStrong[2]![j]! != j || autStrong[3]![j]! != j ||
        autStrong[4]![j]! != j) = true := by
  decide +kernel

theorem fixed_check :
    fixedCount 315 autStrong[0]! = 15 ∧ fixedCount 315 twoAArr = 11 ∧
      fixedCount 315 outerArr = 21 := by
  decide +kernel

end CFSG.ComponentClassification.J2Cover
