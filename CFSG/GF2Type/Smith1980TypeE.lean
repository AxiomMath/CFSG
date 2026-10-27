module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Open
open scoped MatrixGroups

@[expose] def Smith1980TypeEStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      ∀ w : ℕ,
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * w) →
        ∀ (Mbar : Type) [Group Mbar],
          timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
          (w = 10 → Nonempty (generalizedFitting Mbar ≃* timmesfeldPSU 6) →
            LieModel G .twistedE6 0 2 1) ∧
          (w = 10 → Nonempty (generalizedFitting Mbar ≃* PSL(6, ZMod 2)) →
            LieModel G .E6 0 2 1) ∧
          (w = 16 → IsSimpleGroup Mbar →
            (∃ t : Mbar, orderOf t = 2 ∧
              IsExtraspecialPGroup 2 (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) ∧
              Nat.card (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
              timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar)))
                (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) →
            LieModel G .E7 0 2 1) ∧
          (w = 28 → IsSimpleGroup Mbar →
            (∃ t : Mbar, orderOf t = 2 ∧
              IsExtraspecialPGroup 2 (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) ∧
              Nat.card (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
              timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar)))
                (timmesfeldOmegaPlus 6)) →
            LieModel G .E8 0 2 1)

end CFSG.GF2Type
