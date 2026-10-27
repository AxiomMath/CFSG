module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsL5
public import CFSG.Quasithin.H13.StatementsL5C

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj)
open scoped IsMulCommutative

@[expose] def Stmt3_2_9C_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    L = conjClosure L T → V₀ = conjClosure V₀ T →
    (∃ _ : IsMulCommutative ↥V₀,
      ¬ IsFFModule (V := ↥V₀) (Subgroup.normalizer ((autOn L V₀ : Set (MulAut ↥V₀))))) →
      ∃ _ : IsMulCommutative ↥V₀,
        (∃ n : ℕ, 1 < n ∧ LieModel ↥(autOn L V₀) .PSL 2 2 (2 * n) ∧
          BinaryOrthogonalFour (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n ∧
          qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ≤ (2 : ℚ) ∧
          (1 : ℚ) < qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ∧
          qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ≤ (3 / 2 : ℚ)) ∨
        (∃ n : ℕ, BinaryNaturalSU3 (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n ∧
          qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) = (2 : ℚ) ∧
          qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) = (2 : ℚ)) ∨
        (∃ f : ℕ, BinaryNaturalSz (V := ↥V₀) (autOn L V₀) ⊤ ⊥ f ∧
          qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) = (2 : ℚ) ∧
          qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) = (2 : ℚ)) ∨
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 1 ≤ n ∧
          Nat.card K = 2 ^ (2 * n) ∧
          (LieModel ↥(autOn L V₀) .PSL 3 2 (2 * n) ∨
            Nonempty (↥(autOn L V₀) ≃* ↥(StatedSL 3 K))) ∧
          Nat.card V₀ = 2 ^ (9 * n) ∧ (2 : ℚ) < qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ∧
          qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) = (5 / 4 : ℚ) ∧
          ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L V₀),
            (FFModel.twistTensor n (StatedSL 3 K)).RealizesVia (V := ↥V₀) (autOn L V₀) ⊤ ⊥ π ∧
            NoGraphAutomorphism π (autOn T V₀)) ∨
        (Nonempty (↥(autOn (L ⊔ T) V₀) ≃* MulAut ↥NativeSporadic.M12) ∧
          Nat.card V₀ = 2 ^ 10 ∧ (2 : ℚ) < qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ∧
          (1 : ℚ) < qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀)) ∨
        (Group.IsPerfect ↥(autOn L V₀) ∧ Nat.card (Subgroup.center ↥(autOn L V₀)) = 3 ∧
          Nonempty (↥(autOn L V₀) ⧸ Subgroup.center ↥(autOn L V₀) ≃* NativeSporadic.M22) ∧
          Nat.card V₀ = 2 ^ 12 ∧ (1 : ℚ) < qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀)) ∨
        (Nonempty (↥(autOn L V₀) ≃* NativeSporadic.M22) ∧ Nat.card V₀ = 2 ^ 10 ∧
          (2 : ℚ) ≤ qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ∧
          (1 : ℚ) < qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ∧
          (MathieuCocode22 (V := ↥V₀) (autOn L V₀) ⊤ ⊥ →
            (2 : ℚ) < qOf (V := ↥V₀) (autOn (L ⊔ T) V₀))) ∨
        (Nonempty (↥(autOn L V₀) ≃* NativeSporadic.M23) ∧ Nat.card V₀ = 2 ^ 11 ∧
          (2 : ℚ) < qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ∧
          (1 : ℚ) < qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀)) ∨
        (Nonempty (↥(autOn L V₀) ≃* NativeSporadic.M24) ∧ Nat.card V₀ = 2 ^ 11 ∧
          (2 : ℚ) < qOf (V := ↥V₀) (autOn (L ⊔ T) V₀) ∧
          (1 : ℚ) < qhatOf (V := ↥V₀) (autOn (L ⊔ T) V₀))

end CFSG.Quasithin.H13
