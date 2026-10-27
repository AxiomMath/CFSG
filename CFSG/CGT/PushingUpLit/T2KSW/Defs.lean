module

public import CFSG.CGT.PushingUpLit.T2K.FiveB

public section

namespace CFSG.CGT.PushingUpLit.T2KSW

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement

@[expose] def ClassLETwo {G : Type} [Group G] (T : Subgroup G) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ⁅⁅a, b⁆, c⁆ = 1

abbrev Ec {G : Type} [Group G] (L T : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.centralizer (L : Set G)

abbrev Rl {G : Type} [Group G] (L T : Subgroup G) : Subgroup G := T ⊓ L

abbrev Dc {G : Type} [Group G] (L T : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.centralizer (blockU L : Set G)

@[expose] def Print55ClassTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ), Sec4 G L M T n →
    Ec L T ≠ ⊥ → ClassLETwo T → False

@[expose] def Print55ClassThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ), Sec4 G L M T n →
    Ec L T ≠ ⊥ → ¬ ClassLETwo T → False

theorem print55_of_split (h2 : Print55ClassTwo) (h3 : Print55ClassThree) : T2K.Print55 := by
  intro G _ _ L M T n hs hE N R _
  by_cases hc : ClassLETwo T
  · exact h2 G L M T n hs hE hc
  · exact h3 G L M T n hs hE hc

end CFSG.CGT.PushingUpLit.T2KSW
