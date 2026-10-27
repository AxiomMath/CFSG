module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Main
public import CFSG.GH74.GLS.Stage2.Signalizer.L199

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem prop_4_3E_of_hyp (hOut : L34DiagClosure)
    (hHyp : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → E4Hyp G z k) : Prop4_3E := by
  intro G _ _ z k S ctx H₀ H₁ _ hz p X sig hN
  have ha := prop_4_1a_of L199.ig_19_9 G z k S ctx H₀ H₁ hz p X sig
  have hb := prop_4_1b_of L199.ig_19_9 G z k S ctx H₀ H₁ hz p X sig
  have hz2 : zSec z H₀ hz H₁ * zSec z H₀ hz H₁ = 1 := by
    have h := orderOf_zSec ctx.orderOf_z hz H₁ sig.odd
    have h1 := pow_orderOf_eq_one (zSec z H₀ hz H₁)
    rw [h, pow_two] at h1
    exact h1
  exact prop4_3E_core (hHyp G z k S ctx) hOut
    (c := { sec := SecOfG.of_sig4B sig, A4 := sig.A, z2 := hz2, op := sig.op, a41 := ha, b41 := hb }) hN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
