module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableITrue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

section Cert


theorem isShape_centralizer_b (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoTimesA8 ↥(P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) := by
  obtain ⟨-, -, ⟨-, hcard, hcl⟩, -⟩ := invClasses_classSpec hP
  have hXeq : closure (elemW '' {w | w ∈ blkData2.gens}) =
      P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) := hcl
  have hX : Nat.card ↥(closure (elemW '' {w | w ∈ blkData2.gens})) = 80640 := by
    rw [hXeq]
    exact hcard
  rw [← hXeq]
  exact tableI2_shape hX hXeq

end Cert

end CFSG.EvenSporadicStandard.HNRecog
