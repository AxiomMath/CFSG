module

public import CFSG.LieType.SeitzGeneration.HyperIrrFinal
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open

theorem hyperExFor_linear : HyperExFor fun d => IsLinearIndex d.1 :=
  SeitzHyperLie.toEx seitzHyperLieLinear_unconditional

theorem hyperExFor_classical_of_families (hl : HyperExFor fun d => IsLinearIndex d.1)
    (hu : HyperExFor fun d => IsUnitaryIndex' d.1)
    (hs : HyperExFor fun d => IsSymplecticIndex d.1)
    (ho : HyperExFor fun d => IsOrthogonalIndex d.1) :
    HyperExFor fun d => IsClassicalIndex d.1 := by
  refine SeitzHyperLieEx.of_cover
    (S₁ := fun d _ _ => IsLinearIndex d.1 ∨ IsUnitaryIndex' d.1)
    (S₂ := fun d _ _ => IsSymplecticIndex d.1 ∨ IsOrthogonalIndex d.1)
    (fun d _ _ h => ?_)
    (SeitzHyperLieEx.of_cover (fun _ _ _ h => h) hl hu)
    (SeitzHyperLieEx.of_cover (fun _ _ _ h => h) hs ho)
  have h4 := (isClassicalIndex_iff ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1).1 h
  tauto

end CFSG.LieType.SeitzGeneration
