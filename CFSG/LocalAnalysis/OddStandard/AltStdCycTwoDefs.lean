module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup

@[expose] def FourPointBalance {G : Type} [Group G] (L : Subgroup G) {n : ℕ}
    (θ : L ≃* alternatingGroup (Fin n)) : Prop :=
  ∀ e : L, orderOf e = 2 →
    ((θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).support.card = 4 →
      CFSG.oddCore (centralizer ({(e : G)} : Set G)) = ⊥

@[expose] def CycTwoBigFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, Odd n → 9 ≤ n → ∀ θ : L ≃* alternatingGroup (Fin n), FourPointBalance L θ →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) → 4 ≤ Nat.card S → False

structure OrderTwo (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) : Prop where
  std : StandardSetting G L
  odd : Odd n
  hn : 9 ≤ n
  bal4 : FourPointBalance L θ
  cyc : AltStdBal.Cyc L Q z
  card : Nat.card Q = 2

@[expose] def CycTwoShapeThreeFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z u : G), OrderTwo G L Q n θ z →
      u ∈ centralizer ({z} : Set G) → u ∉ L ⊔ centralizer (L : Set G) → u ^ 2 = z → False

@[expose] def CycTwoInnerLargeFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwo G L Q n θ z → 13 ≤ n →
      centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) → False

@[expose] def CycTwoInnerSmallFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwo G L Q n θ z → n ≤ 11 →
      centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) → False

@[expose] def CycTwoShapeTwoLargeFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z u : G), OrderTwo G L Q n θ z → 13 ≤ n →
      u ∈ centralizer ({z} : Set G) → u ∉ L ⊔ centralizer (L : Set G) → u ^ 2 = 1 → False

@[expose] def CycTwoShapeTwoElevenFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (θ : L ≃* alternatingGroup (Fin 11))
    (z u : G), OrderTwo G L Q 11 θ z →
      u ∈ centralizer ({z} : Set G) → u ∉ L ⊔ centralizer (L : Set G) → u ^ 2 = 1 → False

@[expose] def CycTwoShapeTwoNineFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (θ : L ≃* alternatingGroup (Fin 9))
    (z u : G), OrderTwo G L Q 9 θ z →
      u ∈ centralizer ({z} : Set G) → u ∉ L ⊔ centralizer (L : Set G) → u ^ 2 = 1 → False

@[expose] def CycTwoInnerFusionAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwo G L Q n θ z → 13 ≤ n →
      centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) → AltStdSec.FusionAll L z

@[expose] def CycTwoInnerStageM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwo G L Q n θ z → 13 ≤ n →
      centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) → AltStdSec.FusionAll L z →
        ∃ M : Subgroup G, AltStdSec.WreathPair L z n M

@[expose] def CycTwoWreathFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwo G L Q n θ z →
      centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) →
        ∀ M : Subgroup G, AltStdSec.WreathPair L z n M → False

end CFSG.OddStandard.AltStdCycTwo
