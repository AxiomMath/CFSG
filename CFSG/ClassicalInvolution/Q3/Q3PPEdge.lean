module

public import CFSG.ClassicalInvolution.Q3.Q3PPBal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

namespace EdgeData

theorem le_centralizer_prod₁ (h : EdgeData K K₁ K₂ z₁ z₂) :
    K₁ ≤ Subgroup.centralizer ({z₁ * z₂} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have a1 : y * z₁ = z₁ * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.cls₁.subnormal hy)
  have a2 : y * z₂ = z₂ * y := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer₂ hy)
  calc y * (z₁ * z₂) = (y * z₁) * z₂ := by rw [mul_assoc]
    _ = z₁ * (y * z₂) := by rw [a1, mul_assoc]
    _ = z₁ * (z₂ * y) := by rw [a2]
    _ = (z₁ * z₂) * y := by rw [mul_assoc]

end EdgeData

end Edge

section Residual

@[expose] def AlphaCent3EdgesAtSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    RouteD3Setup K z → (∃ a b : G, a * b ≠ b * a) →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), EdgeData K K₁ K₂ z₁ z₂ →
        alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥

end Residual

end CFSG.ClassicalInvolution.Q3.Q3PP
