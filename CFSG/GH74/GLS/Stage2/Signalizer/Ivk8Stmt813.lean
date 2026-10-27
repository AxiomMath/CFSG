module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

@[expose] def IVK_8_13_lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H J : Subgroup G, H ≠ ⊤ → IsCompIn H J → orderOf z = 2 →
      z ∈ normalizer (J : Set G) → ⁅J, zpowers z⁆ = J →
      ∀ (p : ℕ) (P : Subgroup G), p.Prime → p ≠ 2 → IsPGroup p ↥P →
        P ≤ H ⊓ normalizer (J : Set G) → (∀ x ∈ P, z * x = x * z) →
        (∀ c ∈ H ⊓ normalizer (J : Set G), c * z = z * c → c ∈ normalizer (P : Set G)) →
        ¬ P ≤ centralizer (J : Set G) →
        (∀ x ∈ H ⊓ normalizer (J : Set G), ⁅x, z⁆ ∈ J ⊔ centralizer (J : Set G)) ∧
        ((∃ x ∈ P, P ≤ zpowers x ⊔ centralizer (J : Set G)) ∨
          (IsL34Quotient ↥J ∧ p = 3 ∧ (P ⊓ centralizer (J : Set G)).relIndex P = 9 ∧
            InducesUnitaryAut z J))

@[expose] def UnitaryFix {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (F₄ : Type) (_ : Field F₄) (_ : Finite F₄), Nat.card F₄ = 4 ∧
    Nonempty (↥(fixSub α) ≃* StatedProj (StatedSU 3 2 F₄))

@[expose] def KFixOK (k : Kind) {Y : Type} [Group Y] (α : MulAut Y) : Prop :=
  ∀ T : Subgroup Y, T ≤ fixSub α → IsSimpleGroup ↥T → (∃ a b : ↥T, a * b ≠ b * a) →
    KindFactorAll k ↥T

@[expose] def KAY (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], F Y → IsSimpleGroup Y → ∀ α : MulAut Y, α * α = 1 → α ≠ 1 →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P → P ≠ ⊥ →
      (∀ e ∈ P, e * α = α * e) →
      (∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) →
      (∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) ∧
        (IsCyclic ↥P ∨ (LieModel Y .PSL 3 2 2 ∧ p = 3 ∧ UnitaryFix α))

@[expose] def KAYk (k : Kind) (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], F Y → IsSimpleGroup Y → ∀ α : MulAut Y, α * α = 1 → α ≠ 1 →
    KFixOK k α → ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup (MulAut Y), IsPGroup p ↥P → P ≠ ⊥ →
      (∀ e ∈ P, e * α = α * e) →
      (∀ c ∈ fixSub α, Odd (orderOf c) → MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) →
      (∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) ∧
        (IsCyclic ↥P ∨ (LieModel Y .PSL 3 2 2 ∧ p = 3 ∧ UnitaryFix α))

@[expose] def Cell813 (F : (Y : Type) → [Group Y] → Prop) : Prop := ∀ k : Kind, KAYk k F

theorem kayk_of_kay {F : (Y : Type) → [Group Y] → Prop} (h : KAY F) : Cell813 F :=
  fun _ Y _ _ hF hs α h2 h1 _ p hp hp2 P hP hP1 hcomm hnorm =>
    h Y hF hs α h2 h1 p hp hp2 P hP hP1 hcomm hnorm

structure Cells813 : Prop where
  alt : Cell813 FAlt
  spor : Cell813 FSpor
  mcly : Cell813 FMcLy
  two : Cell813 FTwo
  l2 : Cell813 FL2
  l3 : Cell813 FL3
  u3 : Cell813 FU3
  sp4 : Cell813 FSp4
  g2 : Cell813 FG2
  d4 : Cell813 FD4
  l4 : Cell813 FL4
  u4 : Cell813 FU4
  l5 : Cell813 FL5
  u5 : Cell813 FU5
  ree : Cell813 FRee

@[expose] def KB813 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], LieModel Y .PSL 3 2 2 →
    4 ≤ pRank 2 Y ∧
    (∀ t : Y, orderOf t = 2 → ∀ X : Subgroup (MulAut Y), IsPGroup 3 ↥X →
      X ≤ centralizer ({MulAut.conj t} : Set (MulAut Y)) →
      (∀ c ∈ centralizer ({MulAut.conj t} : Set (MulAut Y)), c ∈ normalizer (X : Set (MulAut Y))) →
      X = ⊥) ∧
    (∀ α : MulAut Y, α * α = 1 → UnitaryFix α →
      (∃ E : Subgroup Y, E ≤ fixSub α ∧ IsElementaryAbelian 3 ↥E ∧ Nat.card ↥E = 9 ∧
        ∀ c ∈ fixSub α, c ∈ normalizer (E : Set Y)) ∧
      ∀ P : Subgroup (MulAut Y), IsPGroup 3 ↥P → (∀ e ∈ P, e * α = α * e) →
        (∀ c ∈ fixSub α, MulAut.conj c ∈ normalizer (P : Set (MulAut Y))) → Nat.card ↥P ≤ 9)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
