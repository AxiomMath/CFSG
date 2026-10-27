module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.GLADefs

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint

@[expose] def Aschbacher1976Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      CFSG.Open.GLASymplecticType
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      (∃ p f m : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 ≤ m ∧
          (p ^ f = 2 ^ m - 1 ∨ p ^ f = 2 ^ m + 1) ∧ LieModel G .PSL 2 p f) ∨
      (NativeSporadic.IsSporadic G .M11 ∨ LieModel G .PSL 3 3 1 ∨ LieModel G .PSU 3 3 1) ∨
      NativeSporadic.IsSporadic G .HS ∨
      (IsExtraspecialPGroup 2
          (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) ∧
        ∃ w : ℕ, 2 ≤ w ∧
          Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
            2 ^ (1 + 2 * w))

end CFSG.GF2Type
