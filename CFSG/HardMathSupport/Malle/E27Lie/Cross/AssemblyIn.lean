module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Residual
public import CFSG.HardMathSupport.Foote.E27.Lie
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcCross

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding TauCeti
open CFSG.HardMathSupport.Curtis.UnitaryLevi (InnerCoveredExcCross InnerCoveredExcCrossOpen
  false_of_exc_cross_of_open)


@[expose] def InnerLeaf (P : LieTypeIndex → Prop) : Prop :=
  ∀ {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X},
    E27Config X K R T z → z ∈ K → ∀ d : ValidLieTypeIndex, P d.1 →
      Nonempty (↥K ≃* (CFSGIndex.lie d).Group) → False

theorem idxExcOpen_le_excCross {i : LieTypeIndex} (h : IdxExcOpen i) : InnerCoveredExcCross i := by
  rcases h with ⟨q, hq, h⟩ | ⟨m, hm⟩
  · refine Or.inl ⟨q, hq, ?_⟩
    rcases h with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact Or.inr (Or.inl ⟨m, hm⟩)

section Certs


theorem e27LieIn_of_leaves (leafChar3 : InnerLeaf IdxChar3) (leafQTwo : InnerLeaf IdxQTwo)
    (leafExc : InnerLeaf InnerCoveredExcCrossOpen) : E27LieIn := by
  intro X _ _ K R T z h hz d e
  rcases inner_exhaustive d with hd | hd | hd | hd | hd
  · exact false_of_innerCoveredAll h hz d (Or.inl hd) e
  · exact false_of_innerCoveredAll h hz d (Or.inr hd) e
  · exact leafChar3 h hz d hd e
  · exact leafQTwo h hz d hd e
  · exact false_of_exc_cross_of_open (fun h hz d hd e => leafExc h hz d hd e) h hz d
      (idxExcOpen_le_excCross hd) e

end Certs

end CFSG.HardMathSupport.Malle.E27Lie
