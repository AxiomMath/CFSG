module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def hypDiag {K : Type*} [Field K] (a k : ℕ) (α β γ : K) :
    Matrix (HypIndex a k) (HypIndex a k) K :=
  Matrix.diagonal (Sum.elim (fun _ => α) (Sum.elim (fun _ => β) (fun _ => γ)))

end CFSG.LieType.SemisimpleCentralizers.OrderThree
