module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three

@[expose] def D4ThreeGraphOuter :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 3] (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ), 0 < ε → ε < 3 →
      ∀ α : MulAut (adjointGroup Tag.D4 K),
        α = MulAut.conj g * (exactNormalAut Tag.D4 K a (RingEquiv.refl K) 0 * d4Graph K ε) →
        α ^ 3 = 1 → PerfectInLayer α ∨ CFSG.Open.GLAPPrimeCoreOf 3 (fixSubgroup α) = ⊥

end CFSG.HardMathSupport.Dickson.DefCharOuter
