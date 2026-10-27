module

public import CFSG.GH74.GLS.SP.Identify
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.GH74.GLS.Stage4.HexD4Comm

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section Facts

variable {G : Type} [Group G]

@[expose] def OrthPair (root : ℤ → Subgroup G) : Prop :=
  ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a

@[expose] def SharedInv (root : ℤ → Subgroup G) : Prop :=
  ∃ z : G, orderOf z = 2 ∧ z ∈ root 1 ⊔ root (-1) ∧ z ∈ root 4 ⊔ root (-4)

@[expose] def LongA2 (root : ℤ → Subgroup G) : Prop :=
  (∀ x ∈ root 2, ∀ y ∈ root 4, x * y = y * x) ∧ (∀ x ∈ root 4, ∀ y ∈ root 6, x * y = y * x) ∧
    ∀ x ∈ root 2, ∀ y ∈ root 6, ⁅x, y⁆ ∈ root 4

@[expose] def RootOrdersD4a (root : ℤ → Subgroup G) (q : ℕ) : Prop :=
  ∀ i : ℤ, 1 ≤ i → i ≤ 6 → Nat.card ↥(root i) = if i % 2 = 1 then q ^ 3 else q

end Facts

end CFSG.GH74.GLS.Stage4.Hex
