module

public import CFSG.GF2Type.Smith1979CharTwo

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Open

@[expose] def Smith1979StatementCharTwoKP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ z : G, orderOf z = 2 →
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

theorem smith1979Conclusion_of_charTwoKP (h : Smith1979StatementCharTwoKP) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharTwoType G)
    (hKP : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) : Smith1979Conclusion G :=
  h G hnonab hchar hKP

@[expose] def Smith1979WidthsFourSixCharTwoKP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      ∀ w : ℕ,
        Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
          2 ^ (1 + 2 * w) →
        (w = 4 →
          LieModel G .PSL 6 2 1 ∨ LieModel G .PSU 6 2 1 ∨ LieModel G .POmegaPlus 4 2 1 ∨
            LieModel G .POmegaMinus 4 2 1 ∨ LieModel G .trialityD4 0 2 1 ∨
            LieModel G .POmegaPlus 4 3 1 ∨ NativeSporadic.IsSporadic G .Co2 ∨
            NativeSporadic.IsSporadic G .Co1 ∨ NativeSporadic.IsSporadic G .Th ∨
            NativeSporadic.IsSporadic G .HN) ∧
        (w = 6 →
          LieModel G .PSL 8 2 1 ∨ LieModel G .PSU 8 2 1 ∨ LieModel G .POmegaPlus 5 2 1 ∨
            LieModel G .POmegaMinus 5 2 1 ∨ NativeSporadic.IsSporadic G .J4 ∨
            NativeSporadic.IsSporadic G .Fi24Prime)

end CFSG.GF2Type
