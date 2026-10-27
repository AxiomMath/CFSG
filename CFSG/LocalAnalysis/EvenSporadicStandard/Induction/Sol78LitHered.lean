module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Cor23S
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Lemma36

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.SignalizerFunctorTheorem (IsSectionOf)

@[expose] def Sol78BThmAt (G : Type) [Group G] [Finite G] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → CFSG.oddCore G = ⊥ →
    ∀ u : G, orderOf u = 2 → BTheoremAt u

@[expose] def Sol78BThmHered : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Balance.UHered G → Sol78BThmAt G

@[expose] def Sol78Thm46FSAt (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ∀ P : Subgroup Y, SolStd P →
      CFSG.IsQuasisimple ↥P →
      ((∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 n) ∨
        IsSporadic (↥P ⧸ center ↥P) .Suz ∨ IsSporadic (↥P ⧸ center ↥P) .He) →
      (IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P))) →
        (∃ m : ℕ, 2 ≤ m ∧ LieModel ↥N' .PSL 3 2 (2 * m)) ∨
          (LieModel ↥P .PSL 3 2 2 ∧ IsSporadic ↥N' .Suz) ∨
          (IsKleinFour ↥(center ↥P) ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 ∧
            IsSporadic ↥N' .He) ∨
          (Nonempty (↥(center ↥P) ≃* Multiplicative (ZMod 4)) ∧
            LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 ∧ IsSporadic ↥N' .ONan ∧ P ≤ N')

@[expose] def Sol78Thm46FSHered : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → Sol78Thm46FSAt Y

@[expose] def Sol78Thm412FSAt (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ∀ P : Subgroup Y, SolStd P →
      CFSG.IsQuasisimple ↥P → (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .G2 0 2 n) →
        (∃ m : ℕ, 2 ≤ m ∧ LieModel ↥N' .G2 0 2 (2 * m)) ∨
          (LieModel ↥P .G2 0 2 2 ∧ IsSporadic ↥N' .Co1)

@[expose] def Sol78Thm412FSHered : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → Sol78Thm412FSAt Y

@[expose] def Sol78Hyp12LieAt (Y : Type) [Group Y] [Finite Y] : Prop :=
  ∀ (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ∀ L' : Subgroup Y, SolStd L' →
      CFSG.IsQuasisimple ↥L' → Even (Nat.card ↥(center ↥L')) →
        (LieModel (↥L' ⧸ center ↥L') .PSU 6 2 1 → IsSporadic ↥N' .Fi22) ∧
          (LieModel (↥L' ⧸ center ↥L') .twistedE6 0 2 1 → IsSporadic ↥N' .B)

@[expose] def Sol78Hyp12LieHered : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → Sol78Hyp12LieAt Y

@[expose] def Sol78Thm21At (G : Type) [Group G] [Finite G] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    CFSG.oddCore G = ⊥ → ∀ S T : Subgroup G, IsPGroup 2 S →
    IsPGroup 2 T → ⁅S, T⁆ ≤ S ⊓ T → ∀ K : Subgroup G, IsCompIn K (centralizer (S : Set G)) →
      layerIn (K ⊓ centralizer (T : Set G)) ≤ layerIn (centralizer (T : Set G)) ∧
        (T ≤ centralizer (K : Set G) →
          ∃ M : Subgroup G, IsCompIn M (centralizer (T : Set G)) ∧
            IsCompIn K (centralizer (S : Set G) ⊓ conjClosure M S))

@[expose] def Sol78Thm21Hered : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Balance.UHered G → Sol78Thm21At G

@[expose] def Sol78Cor23SHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Cor23SAt H

@[expose] def Sol78Cor23SSec (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSectionOf X H → Cor23SAt X

theorem Sol78Cor23SHered.sec (h : Sol78Cor23SHered) {H : Type} [Group H] [Finite H]
    (hH : Balance.UHered H) : Sol78Cor23SSec H :=
  fun X _ _ hX => h X (hH.of_section hX)

end CFSG.EvenSporadicStandard.Induction
