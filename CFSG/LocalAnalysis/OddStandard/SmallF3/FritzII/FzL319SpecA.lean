module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Spec

public section

namespace CFSG.OddStandard.SmallF3.FritzII

@[expose] def FzAutW (t s l : MulAut FzUT) : Prop :=
  ∀ α : FzElt ≃ FzElt, (∀ x y, α (fzMulC t s l x y) = fzMulC t s l (α x) (α y)) →
    ∀ x, fzInW t (α x) ↔ fzInW t x

@[expose] def FzClassSpecA : Prop :=
  ∀ t s l : MulAut FzUT, FzValidTriple t s l →
    (∀ x₁, FzValidX t l x₁ → FzShape t s l x₁) ∨ FzAutW t s l

end CFSG.OddStandard.SmallF3.FritzII
