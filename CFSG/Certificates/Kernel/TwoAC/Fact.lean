module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.KC.BM.TwoAC

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

@[expose] def wW (A B : MatB) : MatB :=
  A * B ^ 2 * A * B * A * B ^ 2 * A * B ^ 2 * A * B * A * B ^ 2 * A * B ^ 2

@[expose] def xW (A B : MatB) : MatB := wW A B ^ 17

@[expose] def bW (A B : MatB) : MatB := wW A B ^ 2

@[expose] def gW (A B : MatB) : MatB := B ^ 2 * A * B * A * B

@[expose] def hW (A B : MatB) : MatB := B ^ 2 * A * B ^ 2 * A * B

@[expose] def aW (A B : MatB) : MatB := (xW A B * hW A B * xW A B * gW A B) ^ 2

@[expose] def TwoACFact (A B : MatB) : Prop :=
  xW A B ^ 2 = 1 ∧ (xW A B - 1).rank = 1860 ∧ aW A B ^ 2 = 1 ∧ bW A B ^ 17 = 1 ∧
    (aW A B * bW A B) ^ 13 = 1 ∧ aW A B * xW A B = xW A B * aW A B ∧
    bW A B * xW A B = xW A B * bW A B ∧
    ∃ T₁ T₂ : MatB, T₁.rank ≤ 1 ∧ T₂.rank ≤ 78 ∧
      ∀ M : MatB, M * aW A B = aW A B * M → M * bW A B = bW A B * M →
        ∃ c : Fin 4 → ZMod 2, M = c 0 • 1 + c 1 • xW A B + c 2 • T₁ + c 3 • T₂

end CFSG.KC.BM.TwoAC

end
