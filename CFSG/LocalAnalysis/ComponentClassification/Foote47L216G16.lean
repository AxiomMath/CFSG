module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Data.Rat.Floor
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.Foote47L216

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.FooteLit CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private abbrev PSL216 : Type :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)

end CFSG.ComponentClassification.Foote47L216
