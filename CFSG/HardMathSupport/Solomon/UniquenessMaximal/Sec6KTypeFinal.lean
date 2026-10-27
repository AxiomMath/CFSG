module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6JKType
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3T
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KFixMain

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem inndiagFieldTrivial_bot : InndiagFieldTrivial (⟨fun _ _ => ⊥⟩ : InndiagVocab) :=
  fun _ _ _ _ _ _ hmem => Subgroup.mem_bot.mp hmem

theorem inputKType_of_lemma514 (h514 : Lemma514) : InputKType :=
  inputKType_of_inputs inputL3U3Facts_holds h514
    (inputJLayerType_of_inputs (⟨fun _ _ => ⊥⟩ : InndiagVocab) inputL3T_holds
      (inputL3fix_of_inndiagFieldTrivial inndiagFieldTrivial_bot))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
