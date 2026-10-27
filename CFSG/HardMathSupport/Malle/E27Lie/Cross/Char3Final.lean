module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.ExcUntwistedIndex
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.Char3Small
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Char3ExcTwisted
public import CFSG.HardMathSupport.Foote.E27.LieThree.IndexSpThree
public import CFSG.HardMathSupport.Foote.E27.LieThree.OrthThreeSpec
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.TrialityD4
public import CFSG.HardMathSupport.Foote.E27.QTwoLeaf

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding TauCeti
open CFSG.HardMathSupport.Curtis.UnitaryLevi (InnerCoveredExcCrossOpen)

@[expose] def IdxChar3ExcTwisted (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p = 3 ∧ (i = .twistedE6 q ∨ i = .trialityD4 q)

@[expose] def IdxChar3B3 (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ i = .B 3 q

section Certs

theorem innerLeaf_char3ExcTwisted : InnerLeaf IdxChar3ExcTwisted := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hp, hi⟩ := hd
  obtain ⟨e⟩ := e
  rcases hi with rfl | rfl
  · exact false_of_typeTwistedE6_char_three h hz q hv hp e
  · exact false_of_typeTrialityD4_char_three h hz q hv hp e

theorem innerLeaf_char3Exc : InnerLeaf IdxChar3Exc := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hp, hi⟩ := hd
  rcases hi with hi | hi | hi | hi | hi | hi | hi
  · exact innerLeaf_char3ExcUntwisted h hz ⟨i, hv⟩ ⟨q, hp, Or.inl hi⟩ e
  · exact innerLeaf_char3ExcUntwisted h hz ⟨i, hv⟩ ⟨q, hp, Or.inr (Or.inl hi)⟩ e
  · exact innerLeaf_char3ExcUntwisted h hz ⟨i, hv⟩ ⟨q, hp, Or.inr (Or.inr (Or.inl hi))⟩ e
  · exact innerLeaf_char3ExcUntwisted h hz ⟨i, hv⟩
      ⟨q, hp, Or.inr (Or.inr (Or.inr (Or.inl hi)))⟩ e
  · exact innerLeaf_char3ExcUntwisted h hz ⟨i, hv⟩
      ⟨q, hp, Or.inr (Or.inr (Or.inr (Or.inr hi)))⟩ e
  · exact innerLeaf_char3ExcTwisted h hz ⟨i, hv⟩ ⟨q, hp, Or.inl hi⟩ e
  · exact innerLeaf_char3ExcTwisted h hz ⟨i, hv⟩ ⟨q, hp, Or.inr hi⟩ e

theorem e27LieIn_of_B3 (leafB3 : InnerLeaf IdxChar3B3) (leafQTwo : InnerLeaf IdxQTwo)
    (leafExc : InnerLeaf InnerCoveredExcCrossOpen) : E27LieIn := by
  have leafOrth : InnerLeaf IdxChar3SmallOrth := by
    intro X _ _ K R T z h hz d hd e
    obtain ⟨i, hv⟩ := d
    obtain ⟨q, hp, hf, hi⟩ := hd
    rcases hi with rfl | rfl
    · exact leafB3 h hz ⟨_, hv⟩ ⟨q, hp, hf, rfl⟩ e
    · obtain ⟨e⟩ := e
      exact E27Config.false_of_typeC_three_three h hz q hv ⟨hp, hf⟩ e
  exact e27LieIn_of_leaves (innerLeaf_char3_of_orth_exc leafOrth innerLeaf_char3Exc) leafQTwo
    leafExc

theorem innerLeaf_char3B3 : InnerLeaf IdxChar3B3 := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, hp, hf, rfl⟩ := hd
  obtain ⟨e⟩ := e
  exact E27Config.false_of_typeB_three_three h hz q hv ⟨hp, hf⟩ e

theorem e27LieIn_of_QTwo_exc (leafQTwo : InnerLeaf IdxQTwo)
    (leafExc : InnerLeaf InnerCoveredExcCrossOpen) : E27LieIn :=
  e27LieIn_of_B3 innerLeaf_char3B3 leafQTwo leafExc

open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf in
theorem e27LieIn_of_cells (leafQTwo : InnerLeaf IdxQTwo)
    (hF41 : InnerLeaf (IdxExc .F4 1)) (hF42 : InnerLeaf (IdxExc .F4 2))
    (hE61 : InnerLeaf (IdxExc .E6 1)) (hE62 : InnerLeaf (IdxExc .E6 2))
    (h2E61 : InnerLeaf (IdxExc .twistedE6 1)) (h2E62 : InnerLeaf (IdxExc .twistedE6 2))
    (hE71 : InnerLeaf (IdxExc .E7 1)) (hE72 : InnerLeaf (IdxExc .E7 2))
    (hE81 : InnerLeaf (IdxExc .E8 1)) (hE82 : InnerLeaf (IdxExc .E8 2)) : E27LieIn :=
  e27LieIn_of_QTwo_exc leafQTwo
    (innerLeaf_excOpen_of_cells hF41 hF42 hE61 hE62 h2E61 h2E62 hE71 hE72 hE81 hE82
      innerLeaf_trialityD4)

open CFSG.HardMathSupport.Curtis.Coordinator.ExcLeaf in
theorem e27LieIn_of_exc_cells
    (hF41 : InnerLeaf (IdxExc .F4 1)) (hF42 : InnerLeaf (IdxExc .F4 2))
    (hE61 : InnerLeaf (IdxExc .E6 1)) (hE62 : InnerLeaf (IdxExc .E6 2))
    (h2E61 : InnerLeaf (IdxExc .twistedE6 1)) (h2E62 : InnerLeaf (IdxExc .twistedE6 2))
    (hE71 : InnerLeaf (IdxExc .E7 1)) (hE72 : InnerLeaf (IdxExc .E7 2))
    (hE81 : InnerLeaf (IdxExc .E8 1)) (hE82 : InnerLeaf (IdxExc .E8 2)) : E27LieIn :=
  e27LieIn_of_cells CFSG.HardMathSupport.Foote.E27.innerLeaf_qTwo hF41 hF42 hE61 hE62 h2E61 h2E62
    hE71 hE72 hE81 hE82

end Certs

end CFSG.HardMathSupport.Malle.E27Lie
