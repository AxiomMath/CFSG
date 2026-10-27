module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerFixed
public import CFSG.HardMathSupport.Dickson.Bal207.OrthShapeIdx

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

@[expose] def OrthIdxRankLt (n : ℕ) : TauCeti.LieTypeIndex → Prop
  | .D s _ => s < n
  | .twistedD s _ => s < n
  | .twistedA r _ => r < n
  | .A _ _ => True
  | _ => False

theorem orthFixedIdx_orthCompIdx {m n : ℕ} {i : TauCeti.LieTypeIndex} (h : OrthFixedIdx m i)
    (hmn : m ≤ n) : OrthCompIdx i ∧ OrthIdxRankLt n i := by
  cases i with
  | D s q => exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, lt_of_lt_of_le h.2.2.2 hmn⟩
  | twistedD s q => exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, lt_of_lt_of_le h.2.2.2 hmn⟩
  | twistedA r q =>
    obtain ⟨hq, rfl, h3⟩ := h
    exact ⟨Or.inl ⟨hq, by norm_num, fun h => absurd h.1 (by norm_num)⟩, lt_of_lt_of_le h3 hmn⟩
  | A r q => exact ⟨h, trivial⟩
  | _ => exact h.elim

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix
