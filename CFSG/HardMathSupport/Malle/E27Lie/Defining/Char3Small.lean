module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.Char3Classical
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeUSmall
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti

@[expose] def IdxChar3SmallOrth (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ (i = .B 3 q ∨ i = .C 3 q)

theorem innerLeaf_char3Small_of_orth
    (leaf : InnerLeaf IdxChar3SmallOrth) : InnerLeaf IdxChar3Small := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hp, hf, hi⟩ := hd
  rcases hi with rfl | rfl | rfl | rfl
  · obtain ⟨e⟩ := e
    exact false_of_typeTwistedA_two_three h hz q hv ⟨hp, hf⟩ e
  · obtain ⟨e⟩ := e
    exact false_of_typeTwistedA_three_three h hz q hv ⟨hp, hf⟩ e
  · exact leaf h hz _ ⟨q, hp, hf, Or.inl rfl⟩ e
  · exact leaf h hz _ ⟨q, hp, hf, Or.inr rfl⟩ e

theorem innerLeaf_char3_of_orth_exc
    (leafOrth : InnerLeaf IdxChar3SmallOrth) (leafExc : InnerLeaf IdxChar3Exc) :
    InnerLeaf IdxChar3 :=
  innerLeaf_char3_of_rest (innerLeaf_char3Rest_of_leaves (innerLeaf_char3Small_of_orth leafOrth)
    leafExc)

end CFSG.HardMathSupport.Malle.E27Lie
