module

public import CFSG.GH74.GLS.Stage4.LocalGen
public import CFSG.GH74.GLS.Stage4.RestNotation
public import CFSG.GH74.GLS.Stage4.Statements
public import CFSG.LieType.Steinberg.TwistedD4.Defs
public import CFSG.Timmesfeld.RankTwo.ModelG2Words

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.RankTwo CFSG.GH74.GLS.Stage4.Rest
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

@[expose] def Ch6PlusMatrix (G : Type) [Group G] (p : ℕ) (H : Subgroup G) (r₁ r₂ : G)
    (U : Subgroup G) (root : ℤ → Subgroup G) (z : G) (S K₁ K₂ F P₀ : Subgroup G) (q : ℕ) : Prop :=
  Cor97 p H r₁ r₂ U root ∧ Gen97 p H r₁ r₂ U root z S K₁ K₂ F P₀ ∧ Odd q ∧
    ((5 ≤ q ∧ RootOrdersG2 root q) ∨
      (3 ≤ q ∧ ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = if i % 2 = 1 then q ^ 3 else q)) ∧
    ((∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂) ∧
    (∀ i j : ℤ, 1 ≤ i → i ≤ 6 → 1 ≤ j → j ≤ 6 → i ≠ j → ¬ HEquiv H (root i) (root j)) ∧
    ((∀ x ∈ root 2, ∀ y ∈ root 4, x * y = y * x) ∧ (∀ x ∈ root 4, ∀ y ∈ root 6, x * y = y * x) ∧
      (∀ x ∈ root 2, ∀ y ∈ root 6, ⁅x, y⁆ ∈ root 4))

end CFSG.GH74.GLS.Stage4.Hex
