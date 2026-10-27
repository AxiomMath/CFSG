module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSL
public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSp
public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsOrth

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem mcltf_facts_of_isMcLaughlinGroup {W : Type} [Group W] (h : IsMcLaughlinGroup W) :
    mcltf_Facts W := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact mcltf_facts_of_mulEquiv e (mcltf_facts_statedSL hn)
  · exact mcltf_facts_of_mulEquiv e (mcltf_facts_statedSp hn)
  · exact mcltf_facts_of_mulEquiv e (mcltf_facts_glaPlus hn)
  · exact mcltf_facts_of_mulEquiv e (mcltf_facts_glaMinus hn)
  · exact mcltf_facts_of_mulEquiv e (mcltf_facts_perm hn)

theorem inputMcLaughlinTypeFacts_holds : InputMcLaughlinTypeFacts :=
  fun _ _ _ h => mcltf_facts_of_isMcLaughlinGroup h

end CFSG.HardMathSupport.Solomon.Coordinator
