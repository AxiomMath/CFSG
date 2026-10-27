module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.D5
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD2

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem card_le_eight_of_isPGroup_of_pairOrder_N10_one (hC : CentData z ι)
    (hx : IsConj z (ι τ₀)) (hP2 : ¬ IsConj z (z * ι τ₀))
    (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ centralizer (Agrp ι : Set G)) (hQx : Q ≤ centralizer ({z * ι τ₀} : Set G)) :
    Nat.card Q ≤ 8 := by
  obtain ⟨g, hg, hg1⟩ := exists_gElt_sq_one hC hx hP2
  exact card_le_eight_of_isPGroup hC hP2 hg hg1
    (GElt.not_isConj_z_of_pairOrder_N10_one hC hx hP2 hp hg) hQ hQA hQx

end CFSG.OddStandard.AltStdSec.SwapPartner
