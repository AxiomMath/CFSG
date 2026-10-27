module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Blueprint

@[expose] def SocleTransitive (P : ∀ (F : Type) [Group F], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G) [N.Normal] [IsSimpleGroup ↥N],
    (∃ a b : ↥N, a * b ≠ b * a) → Subgroup.centralizer (N : Set G) = ⊥ → P ↥N →
      ∀ Δ : Set (Subgroup G), PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ →
        (∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → z ∈ N) →
          ∀ J ∈ Δ, ∀ L ∈ Δ, ∃ g : G, conjSub g J = L

@[expose] def IsL2Sq (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ LieModel F .PSL 2 p f

@[expose] def IsL3Ge5 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧ LieModel F .PSL 3 p f

@[expose] def IsU3Ge5 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧ LieModel F .PSU 3 p f

@[expose] def IsU33 (F : Type) [Group F] : Prop :=
  LieModel F .PSU 3 3 1

@[expose] def IsM12 (F : Type) [Group F] : Prop :=
  NativeSporadic.IsSporadic F .M12

@[expose] def IsSp62 (F : Type) [Group F] : Prop :=
  LieModel F .PSp 3 2 1

@[expose] def IsO8p2 (F : Type) [Group F] : Prop :=
  LieModel F .POmegaPlus 4 2 1

@[expose] def SocleType (F : Type) [Group F] : Prop :=
  IsL2Sq F ∨ IsL3Ge5 F ∨ IsU3Ge5 F ∨ IsU33 F ∨ IsM12 F ∨ IsSp62 F ∨ IsO8p2 F

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
