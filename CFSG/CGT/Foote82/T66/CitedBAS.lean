module

public import CFSG.CGT.Foote82.T66.Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev BAS.tvComm (L : Subgroup (GLV V)) (d : GLV V) : Submodule (ZMod 2) V :=
  commSpace (Subgroup.zpowers d) (commSpace L ⊤) ⊔ tildeVBot L

@[expose] def BASThreeA6 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (α : Y →* alternatingGroup (Fin 6)),
    Function.Surjective α → ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ →
      α.ker ≤ Subgroup.center Y →
      Odd (Nat.card α.ker) → α.ker ≠ ⊥ →
      ∀ δ : Y ≃* Y, (∀ y, δ (δ y) = y) → (∃ y, δ y ≠ y) →
        ∃ y : Y, 2 < orderOf (δ y * y⁻¹) ∧ Even (orderOf (δ y * y⁻¹))

@[expose] def BASA6NoSix : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (L : Subgroup (GLV V)),
    Nonempty (↥L ≃* alternatingGroup (Fin 6)) → HasIrrTildeV L →
      Module.finrank (ZMod 2) (TildeV L) ≠ 6

@[expose] def BASOmegaEight : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (L : Subgroup (GLV V)),
    IsOmegaMinusModule L 3 → FaithfulTildeV L → HasIrrTildeV L →
    ∀ d ∈ Subgroup.normalizer (L : Set (GLV V)), orderOf d = 2 →
      (∀ l ∈ L, orderOf (d * (l * d * l⁻¹)) ≤ 2 ∨ Odd (orderOf (d * (l * d * l⁻¹)))) →
      Module.finrank (ZMod 2) ↥(BAS.tvComm L d) ≤ Module.finrank (ZMod 2) ↥(tildeVBot L) + 1

@[expose] def BASTIFails : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (L : Subgroup (GLV V)),
    (IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2) → FaithfulTildeV L → HasIrrTildeV L →
    ∀ d ∈ Subgroup.normalizer (L : Set (GLV V)), orderOf d = 2 →
      (∀ l ∈ L, orderOf (d * (l * d * l⁻¹)) ≤ 2 ∨ Odd (orderOf (d * (l * d * l⁻¹)))) →
      Module.finrank (ZMod 2) ↥(tildeVBot L) + 2 ≤ Module.finrank (ZMod 2) ↥(BAS.tvComm L d) →
      ∃ l ∈ L, l * d * l⁻¹ ≠ d ∧ d * (l * d * l⁻¹) = (l * d * l⁻¹) * d ∧
        commSpace (Subgroup.zpowers d) (commSpace L ⊤) ⊓
          commSpace (Subgroup.zpowers (l * d * l⁻¹)) (commSpace L ⊤) ≠ ⊥

@[expose] def BASMaximal : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (L : Subgroup (GLV V)),
    (IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2 ∨ IsOmegaMinusModule L 3) →
    FaithfulTildeV L → HasIrrTildeV L →
    ∀ d ∈ Subgroup.normalizer (L : Set (GLV V)), orderOf d = 2 →
      Module.finrank (ZMod 2) ↥(BAS.tvComm L d) = Module.finrank (ZMod 2) ↥(tildeVBot L) + 1 →
      IsCoatom ((L ⊓ Subgroup.centralizer ({d} : Set (GLV V))).subgroupOf L)

end CFSG.CGT.Foote82
