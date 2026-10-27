module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Open

@[expose] def Smith1980OrthogonalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      ∀ w : ℕ,
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * w) →
        4 ≤ w → Even w →
        ∀ (Mbar : Type) [Group Mbar],
          timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
          ∀ q : QuadraticForm (ZMod 2) (Fin w → ZMod 2), timmesfeldNondegenerate q →
            (Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
              Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) →
            (timmesfeldPlusType q → LieModel G .POmegaPlus ((w + 4) / 2) 2 1) ∧
            (¬ timmesfeldPlusType q → LieModel G .POmegaMinus ((w + 4) / 2) 2 1)

end CFSG.GF2Type
