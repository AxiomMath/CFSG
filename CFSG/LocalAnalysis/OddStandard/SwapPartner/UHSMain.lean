module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSCyc
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StdOfCyclic
import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGTypes

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern
  CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G} {Kh : Subgroup G}

theorem HSCtx.exists_stdHyp (C : HSCtx z ι ιd Kh) [Finite G] {L : Subgroup G}
    (h : CFSG.OddStandard.AltStdBal.Setting G L 10) :
    CFSG.EvenSporadicStandard.StdHyp G Kh ∧ IsSporadic (↥Kh ⧸ center ↥Kh) .HS := by
  exact ⟨exists_stdHyp_of_component_cyclic_setting h (orderOf_x₂ C.frame.cent)
    C.khat.quasisimple C.khat.le C.khat.normal C.isPGroup_center
    (fun U hU hUle => C.isCyclic_of_isPGroup hU hUle), C.khat.hs⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
