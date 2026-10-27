module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenSylow
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenNormalizes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner


theorem e6InnerSylowMono_holds : E6InnerSylowMono := by
  intro K _ _ _ hK E hED hE3
  obtain ⟨φ, hφ, h⟩ := E6Three.e6_exists_conj_bmMono_sylow hK hE3 hED
  refine ⟨φ, hφ, fun X hX => ?_⟩
  obtain ⟨v, -, hv⟩ := h X hX
  exact ⟨v, hv⟩

theorem e6MonoFixNormalizes_holds : E6MonoFixNormalizes :=
  fun _ _ _ _ _ hl hE => E6Three.e6NormalizesR_of_bmMono_fixed hl hE

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
