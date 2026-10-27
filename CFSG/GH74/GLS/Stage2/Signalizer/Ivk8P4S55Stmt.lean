module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

@[expose] def InvSecGroup (k : Kind) (Y : Type) [Group Y] : Prop :=
  ∃ (A : Type) (_ : Group A) (_ : Finite A) (J : Subgroup A), IsComponent J ∧
    Nonempty ((↥J ⧸ center ↥J) ≃* Y) ∧
    ∀ x : A, orderOf x = 2 → ∀ (Z : Type) [Group Z] [IsSimpleGroup Z], ¬ Group.IsSolvable Z →
      IsSection Z ↥(centralizer ({x} : Set A)) → KindFactorAll k Z

structure Mod55 (p : ℕ) {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ)
    (P : Subgroup Γ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  faithful : Function.Injective ρ
  normal : K.Normal
  quasi : IsQuasisimple ↥K
  gh : GHList (↥K ⧸ center ↥K)
  quad : (((ρ a : (V →ₗ[ZMod p] V)ˣ) : V →ₗ[ZMod p] V) - 1) ^ 2 = 0
  acts : ⁅K, zpowers a⁆ ≠ ⊥
  pgrp : IsPGroup p ↥P
  a_mem : a ∈ P
  opbot : ∀ N : Subgroup Γ, N.Normal → IsPGroup p ↥N → N = ⊥

structure Frame55 (k : Kind) (p : ℕ) {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ)
    (P R : Subgroup Γ) : Prop extends Mod55 p ρ K a P where
  rgrp : IsPGroup 2 ↥R
  norm : R ≤ normalizer (P : Set Γ)
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ K) K
  r3 : InvSecGroup k (↥K ⧸ center ↥K)

@[expose] def Concl55 {Γ : Type} [Group Γ] (p : ℕ) (K : Subgroup Γ) : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ LieModel (↥K ⧸ center ↥K) .PSL 3 p n) ∨
    (p = 3 ∧ (IsDoubleCoverOfAlt ↥K 7 ∨ IsDoubleCoverOfAlt ↥K 11))

@[expose] def Cell55 (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (k : Kind) (p : ℕ) (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ)
    (K : Subgroup Γ) (a : Γ) (P R : Subgroup Γ),
    Frame55 k p ρ K a P R → F (↥K ⧸ center ↥K) → Concl55 p K

structure Cells55 : Prop where
  alt : Cell55 FAlt
  spor : Cell55 FSpor
  mcly : Cell55 FMcLy
  two : Cell55 FTwo
  l2 : Cell55 FL2
  l3 : Cell55 FL3
  u3 : Cell55 FU3
  sp4 : Cell55 FSp4
  g2 : Cell55 FG2
  d4 : Cell55 FD4
  l4 : Cell55 FL4
  u4 : Cell55 FU4
  l5 : Cell55 FL5
  u5 : Cell55 FU5
  ree : Cell55 FRee

@[expose] def Frame55Thm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      ¬ Concl51 k S p H P → L52 k S T Tstar p H P →
      ∀ (g : G) (X Y : Subgroup G), Step53 p H P g X Y → TypeOneCase G k →
        ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V)
          (_ : Module (ZMod p) V) (_ : Module.Finite (ZMod p) V)
          (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ) (P' R : Subgroup Γ),
          Frame55 k p ρ K a P' R ∧ (Concl55 p K → L55 k p H)

@[expose] def Case55B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      ¬ Concl51 k S p H P → L52 k S T Tstar p H P →
      ∀ (g : G) (X Y : Subgroup G), Step53 p H P g X Y → ¬ TypeOneCase G k → False

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
