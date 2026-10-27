module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Blocks

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

@[expose] def IsFStar (X : Type) [Group X] : Prop :=
  LieModel (X ⧸ pPrimeCore 2 X) .PSL 2 3 2 ∨ LieModel (X ⧸ pPrimeCore 2 X) .PSL 2 3 4 ∨
    LieModel (X ⧸ pPrimeCore 2 X) .PSL 3 3 1 ∨ LieModel (X ⧸ pPrimeCore 2 X) .PSU 3 3 1 ∨
    SmallF3OmegaQuotient (X ⧸ pPrimeCore 2 X) ∨
    (Nat.card (center (X ⧸ pPrimeCore 2 X)) = 2 ∧
      LieModel ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) .PSU 4 3 1)

structure A2Config (G : Type) [Group G] (x y : G) (X K : Subgroup G) : Prop where
  ox : orderOf x = 2
  oy : orderOf y = 2
  comm : x * y = y * x
  X_le : X ≤ centralizer ({x, y} : Set G)
  X_comp : IsPComponent 2 (X.subgroupOf (centralizer ({x, y} : Set G)))
  K_le : K ≤ centralizer ({y} : Set G)
  K_comp : IsPComponent 2 (K.subgroupOf (centralizer ({y} : Set G)))
  X_le_KK : X ≤ K ⊔ K.map (MulAut.conj x).toMonoidHom

@[expose] def HypA2 (G : Type) [Group G] : Prop :=
  ∀ (x y : G) (X K : Subgroup G), A2Config G x y X K → IsFStar ↥X → IsFStar ↥K

@[expose] def IsResidualA2 (K : Type) [Group K] : Prop :=
  (center K = ⊥ ∧ LieModel K .PSL 2 3 8) ∨
    (∃ m : ℕ, 4 ≤ m ∧ center K = ⊥ ∧ Nonempty (K ≃* alternatingGroup (Fin (2 * m)))) ∨
    NativeSporadic.IsSporadic (K ⧸ center K) .HS ∨
    LieModel (K ⧸ center K) .PSp 2 2 2 ∨ LieModel (K ⧸ center K) .PSL 5 2 1 ∨
    LieModel (K ⧸ center K) .PSU 5 2 1 ∨ LieModel (K ⧸ center K) .G2 0 2 2 ∨
    LieModel (K ⧸ center K) .PSL 4 2 2

@[expose] def NoResidualA2 (G : Type) [Group G] : Prop :=
  ∀ (x y : G) (X K : Subgroup G), A2Config G x y X K → IsFStar ↥X → ¬ IsResidualA2 ↥K

end CFSG.OddStandard.SmallF3.HypA2
