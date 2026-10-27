module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.AssemblyIn
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.ExcReeG2

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti

@[expose] def IdxChar3Rest (i : LieTypeIndex) : Prop :=
  IdxChar3 i ∧ ¬ ∃ m : ℕ, i = .reeG2 m

theorem innerLeaf_char3_of_rest (leafRest : InnerLeaf IdxChar3Rest) :
    InnerLeaf IdxChar3 := by
  intro X _ _ K R T z h hz d hd e
  by_cases hr : ∃ m : ℕ, d.1 = .reeG2 m
  · exact false_of_innerCoveredReeG2 h hz d hr e
  · exact leafRest h hz d ⟨hd, hr⟩ e

end CFSG.HardMathSupport.Malle.E27Lie

end
