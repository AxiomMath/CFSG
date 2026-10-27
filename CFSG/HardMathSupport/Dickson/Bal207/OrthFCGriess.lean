module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthFCArith
public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerFixed

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFC

theorem fixedIdx_of_orthFixedIdx {n : ℕ} {i : TauCeti.LieTypeIndex}
    (h : OrthFix.OrthFixedIdx n i) : FixedIdx i := by
  cases i <;> first
    | exact False.elim h
    | exact ⟨h.1, h.2.1, h.2.2.1⟩
    | exact ⟨h.2.1, h.1⟩
    | exact h

end CFSG.HardMathSupport.Dickson.Bal207.OrthFC

end
