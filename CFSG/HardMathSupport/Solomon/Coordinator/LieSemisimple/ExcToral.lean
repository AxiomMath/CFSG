module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
import CFSG.LieType.AlgebraicGroups.TorusAffineDomain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar

private theorem torusGroup_mul_comm_aux
    {τ : Tag} {K : Type} [Field K] {x y : ModGL τ K} (hx : x ∈ torusGroup τ K)
    (hy : y ∈ torusGroup τ K) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
