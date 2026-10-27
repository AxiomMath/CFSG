module

public import CFSG.GF2Type.Smith1980TypeE

public section

namespace CFSG.GF2Type.SmithTypeE

open CFSG CFSG.Blueprint CFSG.Open
open scoped MatrixGroups

@[expose] def PartA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
        2 ^ (1 + 2 * 10) →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        Nonempty (generalizedFitting Mbar ≃* timmesfeldPSU 6) → LieModel G .twistedE6 0 2 1

@[expose] def PartB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
        2 ^ (1 + 2 * 10) →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        Nonempty (generalizedFitting Mbar ≃* PSL(6, ZMod 2)) → LieModel G .E6 0 2 1

@[expose] def PartC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
        2 ^ (1 + 2 * 16) →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        IsSimpleGroup Mbar →
        (∃ t : Mbar, orderOf t = 2 ∧
          IsExtraspecialPGroup 2 (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) ∧
          Nat.card (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 17 ∧
          timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar)))
            (Equiv.Perm (Fin 3) × timmesfeldOmegaPlus 4)) →
        LieModel G .E7 0 2 1

@[expose] def PartD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 →
      IsExtraspecialPGroup 2
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) →
      Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
        2 ^ (1 + 2 * 28) →
      ∀ (Mbar : Type) [Group Mbar],
        timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({z} : Set G))) Mbar →
        IsSimpleGroup Mbar →
        (∃ t : Mbar, orderOf t = 2 ∧
          IsExtraspecialPGroup 2 (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) ∧
          Nat.card (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar))) = 2 ^ 33 ∧
          timmesfeldQuotientIso (generalizedFitting (Subgroup.centralizer ({t} : Set Mbar)))
            (timmesfeldOmegaPlus 6)) →
        LieModel G .E8 0 2 1

theorem smith1980TypeEStatement_of_parts (hA : PartA) (hB : PartB) (hC : PartC) (hD : PartD) :
    Smith1980TypeEStatement := by
  intro G _ _ _ hnonab z hz hext w hcard Mbar _ hMbar
  refine ⟨fun hw hU => ?_, fun hw hL => ?_, fun hw hs ht => ?_, fun hw hs ht => ?_⟩
  · subst hw
    exact hA G hnonab z hz hext hcard Mbar hMbar hU
  · subst hw
    exact hB G hnonab z hz hext hcard Mbar hMbar hL
  · subst hw
    exact hC G hnonab z hz hext hcard Mbar hMbar hs ht
  · subst hw
    exact hD G hnonab z hz hext hcard Mbar hMbar hs ht

end CFSG.GF2Type.SmithTypeE
