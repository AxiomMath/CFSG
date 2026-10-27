module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec3L34Data {G : Type} [Group G] (x : G) (X : Subgroup G) (y : G) (K : Subgroup G)
    (u : G) (I : Subgroup G) : Prop where
  pocket : Sec3PocketData x X y K
  involution_u : orderOf u = 2
  mem : ∃ c ∈ centralizer ((X ⊔ zpowers x : Subgroup G) : Set G), u = c * y
  component : IsComponentIn I (centralizer ({u} : Set G))
  inFStar : InFStar I

@[expose] def FStarQuotientNoL81 (Y : Type) [Group Y] : Prop :=
  SmallF3OmegaQuotient Y ∨ IsTwoU43 Y ∨
    LieModel Y .PSL 2 3 2 ∨ LieModel Y .PSL 3 3 1 ∨ LieModel Y .PSU 3 3 1

@[expose] def PocketableQuotient (Y : Type) [Group Y] : Prop :=
  LieModel Y .PSp 2 3 1 ∨ LieModel Y .POmegaOdd 3 3 1 ∨ LieModel Y .POmegaPlus 4 3 1 ∨
    LieModel Y .POmegaMinus 4 3 1 ∨ (CFSG.IsQuasisimple Y ∧ IsTwoU43 Y)

@[expose] def Asc82NoQ8InL2 : Prop :=
  ∀ (X : Type) [Group X], (LieModel X .PSL 2 3 2 ∨ LieModel X .PSL 2 3 4) →
    ∀ f : QuaternionGroup 2 →* X, ¬ Function.Injective f

@[expose] def Asc82Omega8PlusPocket : Prop :=
  ∀ (X : Type) [Group X], LieModel X .POmegaPlus 4 3 1 →
    ∀ f : QuaternionGroup 2 →* X, Function.Injective f →
      IsI4PlusIn (⊤ : Subgroup X) (f (QuaternionGroup.a 2))

@[expose] def Asc82Q8Pocket : Prop :=
  ∀ (X : Type) [Group X] [Finite X], PocketableQuotient X →
    ∀ f : QuaternionGroup 2 →* X, Function.Injective f →
      IsI4PlusIn (⊤ : Subgroup X) (f (QuaternionGroup.a 2))

@[expose] def Asc82Thm2Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G) (u : G) (I : Subgroup G),
      Sec3L34Data x X y K u I →
        ⁅CFSG.inSubgroup (CFSG.pCore 2) K, I⁆ = ⊥ ∨ CFSG.inSubgroup (CFSG.pCore 2) K ≤ I

@[expose] def Asc82CommuteStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G) (u : G) (I : Subgroup G),
      Sec3L34Data x X y K u I → ⁅CFSG.inSubgroup (CFSG.pCore 2) K, I⁆ = ⊥ → ⁅K, I⁆ = ⊥

@[expose] def Asc82CommutingPocket : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ (x : G) (X : Subgroup G) (y : G) (K : Subgroup G), Sec3PocketData x X y K →
      ∀ I : Subgroup G, IsComponentIn I (centralizer ({y} : Set G)) → InFStar I →
        ⁅K, I⁆ = ⊥ → False

end CFSG.OddStandard.SmallF3.Omega
