module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.P1
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSkel

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal
  CFSG.Blueprint.NativeSporadic

@[expose] def SwapFrameP2One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z : G) (h : Setting G L 10)
    (d : Cyc L Q z) (ι : Perm (Fin 10) →* G), SwapFrame h d ι → ¬ IsConj z (z * ι τ₀) →
    pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1 →
      ∃ K : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K ∧ IsSporadic (K ⧸ center K) .HS

@[expose] def SwapFrameP2Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (z : G) (h : Setting G L 10)
    (d : Cyc L Q z) (ι : Perm (Fin 10) →* G), SwapFrame h d ι → ¬ IsConj z (z * ι τ₀) →
    pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2 →
      ∃ K : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K ∧ IsSporadic (K ⧸ center K) .HS

theorem shapeTwoTenSwapPartnerStdHS_of_frames (ha : SwapFrameP2One) (hb : SwapFrameP2Two) :
    ShapeTwoTenSwapPartnerStdHS := by
  intro G _ _ L Q z u h d T e ⟨y, hy, hsw, hc⟩
  obtain ⟨ι, F⟩ := exists_swapFrame h d T e hy hsw hc
  by_cases hP : IsConj z (z * ι τ₀)
  · exact (ys04c F hP).elim
  rcases swapFrame_cases F with hp | hp
  · exact ha G L Q z h d ι F hP hp
  · exact hb G L Q z h d ι F hP hp

end CFSG.OddStandard.AltStdSec.SwapPartner
