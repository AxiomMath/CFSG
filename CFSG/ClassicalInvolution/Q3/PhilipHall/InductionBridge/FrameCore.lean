module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameSimple

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge

class FrameCore (G : Type*) [Group G] : Prop where
  center : (∃ a b : G, a * b ≠ b * a) → Subgroup.center G = ⊥
  oddNormal : (∃ a b : G, a * b ≠ b * a) → ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) →
    N = ⊥

instance FrameCore.of_frameSimple (G : Type*) [Group G] [FrameSimple G] : FrameCore G where
  center := FrameSimple.center
  oddNormal := FrameSimple.oddNormal

theorem FrameSimple.of_frameCore {G : Type*} [Group G] [FrameCore G]
    (h : (∃ a b : G, a * b ≠ b * a) → ∀ H : Subgroup G, H.index ≠ 2) : FrameSimple G where
  noIndexTwo := h
  center := FrameCore.center
  oddNormal := FrameCore.oddNormal

end CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge
