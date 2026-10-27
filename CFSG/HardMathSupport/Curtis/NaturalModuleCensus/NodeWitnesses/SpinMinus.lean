module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.CartanB
public import CFSG.LieType.Universal.Spin.Twisted.Extras

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses

open CFSG.AGLEmbedding CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

theorem hubWitnesses_spinMinus {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) :
    HubWitnesses (minusDatum n hirr) :=
  hubWitnesses_of_hubCases (minusDatum_isCTGroupDatum n hirr hn)
    (minusDatum_steinbergExtras n hirr) rfl (hubCases_cartanB (m := n - 1) (by omega))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses
