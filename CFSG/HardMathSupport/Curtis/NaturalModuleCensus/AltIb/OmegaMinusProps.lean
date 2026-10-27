module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusDefs
public import CFSG.LieType.BorelTits.OrthogonalForm

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.AGLEmbedding.LieOut

@[expose] def OmegaMinusSmallSplit : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (b c : F),
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) → ∀ (p : ℕ), (p = 5 ∨ p = 7) → p ∣ Nat.card F - 1 →
    (∀ g : GL (Idx 0) F, g ∈ CFSG.LieType.BorelTits.orthGroup (Qm 0 F b c) → g ^ p = 1 → g = 1) ∧
    NoAp p (↥(Ωm 1 F b c) ⧸ Subgroup.center ↥(Ωm 1 F b c))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
