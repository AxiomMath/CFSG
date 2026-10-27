module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.S1

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

structure Stage1Sem
    (y w : Ω) : Prop where
  adj_x0_y : Δ.Adj x0 y
  ne_x1 : y ≠ x1
  not_adj_x1_y : ¬ Δ.Adj x1 y
  adj_x0_w : Δ.Adj x0 w
  adj_x1_w : Δ.Adj x1 w
  adj_y_w : Δ.Adj y w
  cover : ∀ c, Δ.Adj x0 c → c = x1 ∨ Δ.Adj x1 c ∨ c ∈ MulAction.orbit A1gen y
  card_orbit_y : Nat.card (MulAction.orbit A1gen y) = 28160
  tree : ∃ (r : Ω) (rk : Ω → ℕ), (Δ.Adj x0 r ∧ Δ.Adj x1 r ∧ Δ.Adj y r) ∧
    ∀ v, Δ.Adj x0 v → Δ.Adj x1 v → Δ.Adj y v →
      v = r ∨ ∃ p, (Δ.Adj x0 p ∧ Δ.Adj x1 p ∧ Δ.Adj y p) ∧ Δ.Adj v p ∧ rk p < rk v
  pick : ∀ g, Δ.Adj x0 g → Δ.Adj y g → g = x1 ∨ Δ.Adj x1 g ∨
    ∃ c, (Δ.Adj x0 c ∧ Δ.Adj x1 c ∧ Δ.Adj y c) ∧ Δ.Adj c g

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

end
