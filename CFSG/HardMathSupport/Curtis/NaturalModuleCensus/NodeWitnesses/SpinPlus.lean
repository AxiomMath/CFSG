module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.CartanD
public import CFSG.LieType.CurtisTits.Spin

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses

open CFSG.AGLEmbedding CFSG.LieType.Universal CFSG.LieType.Universal.Spin

theorem hubWitnesses_spinPlus {n : ℕ} {F : Type} [Field F] (hn : 4 ≤ n) :
    HubWitnesses (plusDatum n F (Nat.le_of_succ_le hn)) :=
  hubWitnesses_of_hubCases
    (plusDatum_isCTGroupDatum (Nat.le_of_succ_le hn)
      (plusDatum_iSup_eq_top n F (Nat.le_of_succ_le hn)))
    (plusDatum_steinbergExtras (Nat.le_of_succ_le hn)) rfl (hubCases_cartanD hn)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses
