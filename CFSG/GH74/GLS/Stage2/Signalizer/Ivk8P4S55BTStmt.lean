module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTE16
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

@[expose] def fixSub {Y : Type} [Group Y] (x : MulAut Y) : Subgroup Y where
  carrier := {y | x y = y}
  one_mem' := map_one x
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, ha]

@[expose] def AdmAut (k : Kind) {Y : Type} [Group Y] (x : MulAut Y) : Prop :=
  ∀ (Z : Type) [Group Z] [IsSimpleGroup Z], ¬ Group.IsSolvable Z → IsSection Z ↥(fixSub x) →
    KindFactorAll k Z

@[expose] def AdmRank3 (k : Kind) (Y : Type) [Group Y] : Prop :=
  ∀ E : Subgroup (MulAut Y), IsElementaryAbelian 2 ↥E → (∀ x ∈ E, x ≠ 1 → AdmAut k x) →
    Nat.card ↥E ≤ 8

@[expose] def RankCellK (k : Kind) (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → F Y →
    ¬ KindFactorAll k Y ∧ AdmRank3 k Y

@[expose] def RankCell (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ k : Kind, IsClassicalKind k → RankCellK k F

@[expose] def OutTwoNilp (Y : Type) [Group Y] : Prop :=
  ∃ O : Subgroup (MulAut Y), O.Normal ∧ (MulAut.conj : Y →* MulAut Y).range ≤ O ∧
    (∀ w ∈ O, ∃ m : ℕ, Odd m ∧ w ^ m ∈ (MulAut.conj : Y →* MulAut Y).range) ∧
    ∀ y : MulAut Y, ∃ n : ℕ, y ^ 2 ^ n ∈ O

@[expose] def OutCell (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → F Y → OutTwoNilp Y

@[expose] def OuterFalseNS (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ α : MulAut Y, α ∉ (MulAut.conj : Y →* MulAut Y).range → α ^ p = 1 →
    (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Y, IsPGroup r ↥Q →
      (∀ x ∈ Q, α x ∈ Q) → ∀ x ∈ Q, α x = x) → False

@[expose] def LinkB {G : Type} [Group G] (H P : Subgroup G) (g : G) {Γ : Type} [Group Γ]
    (K : Subgroup Γ) (a : Γ) (P' : Subgroup Γ) (J : Subgroup (HBar H)) : Prop :=
  ∃ (Γ₀ : Type) (_ : Group Γ₀) (_ : Finite Γ₀) (π : ↥H →* Γ₀) (ι : Γ →* Γ₀) (hg : g ∈ H),
    Function.Injective ι ∧ Function.Surjective π ∧ ι.range.Normal ∧ ι.range.index ≤ 2 ∧
    (∀ x : Γ₀, x ∈ normalizer ((K.map ι : Subgroup Γ₀) : Set Γ₀) → x ∈ ι.range) ∧
    ι a = π ⟨g, hg⟩ ∧ P'.map ι = (P.subgroupOf H).map π ∧
    IsComponent J ∧ ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H)) ∧
    ∃ Dl : Subgroup G, Dl ≤ H ∧ Group.IsPerfect ↥Dl ∧
      (Dl.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) = J ∧
      (Dl.subgroupOf H).map π = K.map ι ∧
      ∀ h : ↥H, QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ normalizer (J : Set (HBar H)) →
        (h : G) ∈ normalizer (Dl : Set G)

@[expose] def BridgeB (k : Kind) (p : ℕ) {G : Type} [Group G] (H P : Subgroup G) (g : G)
    (J : Subgroup (HBar H)) : Prop :=
  ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V)
    (_ : Module (ZMod p) V) (_ : Module.Finite (ZMod p) V) (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ)
    (K : Subgroup Γ) (a : Γ) (P' : Subgroup Γ),
    Mod55 p ρ K a P' ∧ InvSecGroup k (↥K ⧸ center ↥K) ∧ LinkB H P g K a P' J

@[expose] def CellV (F : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55E G z k S T Tstar p H P g X Y →
    ∀ (t : G) (q : ℕ) (I Q₁ : Subgroup G), Data5A2 z k S T Tstar p H P t q I Q₁ →
    ∀ J : Subgroup (HBar H), BridgeB k p H P g J → F (↥J ⧸ center ↥J) → False

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
