module

public import Mathlib
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFusion
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public meta import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public meta import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutFixedData

public section

namespace CFSG.GH74.KGroups.TwoM12

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.M12Cover CFSG.Blueprint Subgroup
open scoped commutatorElement
set_option compiler.extract_closed false

@[expose] def gzPerm : Equiv.Perm (Fin 12) := evalCodes [m12gA, m12gB] gzWord

@[expose] def commCheckOn (tabs : Vector (SchreierOrbitState 12) fixedDQ.baseCount)
    (Lc : List (Equiv.Perm (Fin 12))) : Bool :=
  Lc.all fun a => Lc.all fun b =>
    schreierSiftSucceeds (fixedDQ.siftLevels tabs 0) (gzPerm * (a * b * a⁻¹ * b⁻¹) * gzPerm⁻¹)

end CFSG.GH74.KGroups.TwoM12
