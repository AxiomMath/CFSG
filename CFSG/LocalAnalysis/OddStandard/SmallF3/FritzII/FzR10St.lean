module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY10
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316Z1

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups

@[expose] def FzR10Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → FzSylow T₂ →
    t ∉ fzP t x₁ x₂ rho

@[expose] def FzR10Types : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → FzSylow T₂ → t ∉ fzP t x₁ x₂ rho →
    FzZ8 (fourGrp x₁ x₂) (baseGrp x₁ x₂) (fzP t x₁ x₂ rho) ∨
      Nonempty (↥(fzP t x₁ x₂ rho) ≃* FzZ4422) ∨
      (¬ IsMulCommutative (fzP t x₁ x₂ rho) ∧ Nonempty (↥(fzP t x₁ x₂ rho) ≃* SylSL3_4))

@[expose] def FzR10NoA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → FzSylow T₂ → t ∉ fzP t x₁ x₂ rho →
    FzZ8 (fourGrp x₁ x₂) (baseGrp x₁ x₂) (fzP t x₁ x₂ rho) → False

@[expose] def FzR10NoB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → FzSylow T₂ → t ∉ fzP t x₁ x₂ rho →
    Nonempty (↥(fzP t x₁ x₂ rho) ≃* FzZ4422) → False

@[expose] def FzR10Shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → FzSylow T₂ → t ∉ fzP t x₁ x₂ rho →
    Nonempty (↥(fzP t x₁ x₂ rho) ≃* SylSL3_4) →
    ∃ a₁₂ a₂₂ a₃₂ : G, FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂

theorem fzr_y10_of_split (hE : FzR10Excl) (hT : FzR10Types) (hA : FzR10NoA) (hB : FzR10NoB)
    (hS : FzR10Shape) : FzY10Shape := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT2 hsyl
  have ht := hE G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT2 hsyl
  rcases hT G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT2 hsyl ht with h8 | hZ | ⟨-, hC⟩
  · exact (hA G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT2 hsyl ht h8).elim
  · exact (hB G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT2 hsyl ht hZ).elim
  · exact hS G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT2 hsyl ht hC

end CFSG.OddStandard.SmallF3.FritzII
