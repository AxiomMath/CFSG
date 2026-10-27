module

public import CFSG.ClassicalInvolution.RouteD.ExoticShapes

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PSp6Recognition (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .PSp 2 (conjClass K) z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

theorem rowSp6_of_recognition (h : PSp6Recognition p f) (hup : SmallUpgrade p f) :
    RowPiece p f Exotic.ShapeSp6 := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  exact hup G hnab S.odd S.five K z S.cls (h G hnab K z S hS)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
