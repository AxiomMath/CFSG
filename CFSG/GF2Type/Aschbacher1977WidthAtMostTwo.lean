module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint

@[expose] def Aschbacher1977WidthAtMostTwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      ∀ w : ℕ,
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * w) →
        (w = 1 →
          LieModel G .PSL 2 7 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
            NativeSporadic.IsSporadic G .M11 ∨ LieModel G .PSL 3 3 1) ∧
        (w = 2 →
          LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 ∨ LieModel G .PSU 4 3 1 ∨
            LieModel G .G2 0 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
            Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ NativeSporadic.IsSporadic G .M12 ∨
            NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .J3)

end CFSG.GF2Type
