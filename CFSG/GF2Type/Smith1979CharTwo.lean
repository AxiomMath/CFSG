module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Open

@[expose] def Smith1979Conclusion (G : Type) [Group G] [Finite G] : Prop :=
  ∀ z : G, orderOf z = 2 →
    IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
    ∀ w : ℕ,
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
        2 ^ (1 + 2 * w) →
      (w = 3 →
        LieModel G .PSL 5 2 1 ∨ LieModel G .PSU 5 2 1 ∨ NativeSporadic.IsSporadic G .M24 ∨
          NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Suz) ∧
      (w = 4 →
        LieModel G .PSL 6 2 1 ∨ LieModel G .PSU 6 2 1 ∨ LieModel G .POmegaPlus 4 2 1 ∨
          LieModel G .POmegaMinus 4 2 1 ∨ LieModel G .trialityD4 0 2 1 ∨
          LieModel G .POmegaPlus 4 3 1 ∨ NativeSporadic.IsSporadic G .Co2 ∨
          NativeSporadic.IsSporadic G .Co1 ∨ NativeSporadic.IsSporadic G .Th ∨
          NativeSporadic.IsSporadic G .HN) ∧
      (w = 6 →
        LieModel G .PSL 8 2 1 ∨ LieModel G .PSU 8 2 1 ∨ LieModel G .POmegaPlus 5 2 1 ∨
          LieModel G .POmegaMinus 5 2 1 ∨ NativeSporadic.IsSporadic G .J4 ∨
          NativeSporadic.IsSporadic G .Fi24Prime) ∧
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
          (w = 11 → Nonempty (Mbar ≃* NativeSporadic.Co2) → NativeSporadic.IsSporadic G .B) ∧
          (w = 12 → Nonempty (Mbar ≃* NativeSporadic.Co1) → NativeSporadic.IsSporadic G .M)

end CFSG.GF2Type
